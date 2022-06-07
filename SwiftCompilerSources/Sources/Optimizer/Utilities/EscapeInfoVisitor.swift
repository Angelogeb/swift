import SIL

struct EscapeInfoState : HasResult {
  let result: WalkResult
  let followStores: Bool
  let knownType: Type?
  let walkDown: Bool
  
  init(result: WalkResult, followStores: Bool, knownType: Type?, walkDown: Bool = false) {
    self.result = result
    self.followStores = followStores
    self.knownType = knownType
    self.walkDown = walkDown
  }
  
  func with(result: WalkResult) -> EscapeInfoState {
    return EscapeInfoState(result: result, followStores: followStores, knownType: knownType)
  }
  
  func with(knownType: Type?) -> EscapeInfoState {
    return EscapeInfoState(result: result, followStores: followStores, knownType: knownType)
  }
  
  func with(followStores: Bool) -> EscapeInfoState {
    return EscapeInfoState(result: result, followStores: followStores, knownType: knownType)
  }
  
  func with(walkDown: Bool) -> EscapeInfoState {
    return EscapeInfoState(result: result, followStores: followStores, knownType: knownType, walkDown: walkDown)
  }
}

protocol VisitUseFunction : HasState {
  mutating
  func visitUse(operand: Operand, path: SmallProjectionPath, state: State) -> State
}

protocol VisitDefFunction : HasState {
  mutating
  func visitDef(def: Value, path: SmallProjectionPath, state: State) -> State
}



struct EscapeInfoVisitor<V : VisitDefFunction & VisitUseFunction> : DefVisitor, UseVisitor
  where V.State == EscapeInfoState {
  
  typealias State = EscapeInfoState
  
  var visitFunctions: V
  
  init(calleeAnalysis: CalleeAnalysis, visitFunctions: V) {
    self.calleeAnalysis = calleeAnalysis
    self.visitFunctions = visitFunctions
  }
  
  /// Returns true if `object`, or any sub-objects which are selected by `path`, can escape.
  ///
  /// For example, let's assume this function is called with a struct, containing a reference,
  /// and a path of `s0.c*`:
  /// \code
  ///    %value : $Struct<X>                         // path == s0.c*, the initial `object`
  ///    %ref = struct_extract %value, #field0       // path == c*
  ///    %ref1 = struct_extract %value, #field1      // ignored - not selected by path
  ///    %addr = ref_element_addr %ref, #some_field  // path is empty
  ///    %v = load %addr                             // path is empty
  ///    return %v                                   // escaping!
  /// \endcode
  ///
  /// Trivial values are ignored, even if they are selected by `path`.
  mutating func isEscaping(object: Value, path: SmallProjectionPath = SmallProjectionPath()) -> Bool {
    start(forAnalyzingAddresses: false)
    defer { cleanup() }
    
    let state = State(result: .continueWalk, followStores: false, knownType: nil)
    if let (path, state) = shouldRecomputeUp(def: object, path: path, state: state) {
      if object.type.isAddress {
        return walkUp(address: object, path: path, state: state).result == .abortWalk
      } else {
        return walkUp(value: object, path: path, state: state).result == .abortWalk
      }
    }
    return false
  }
  
  mutating
  func shouldRecomputeDown(def: Value, path: SmallProjectionPath, state: State) -> (SmallProjectionPath, State)? {
    if let entry = walkedDownCache[def.hashable, default: CacheEntry()].needWalk(path: path, followStores: state.followStores, knownType: state.knownType) {
      return (entry.path, State(result: state.result, followStores: entry.followStores, knownType: entry.knownType))
    }
    return nil
  }
  
  mutating
  func shouldRecomputeUp(def: Value, path: SmallProjectionPath, state: State) -> (SmallProjectionPath, State)? {
    if let entry = walkedUpCache[def.hashable, default: CacheEntry()].needWalk(path: path, followStores: state.followStores, knownType: state.knownType) {
      return (entry.path, State(result: state.result, followStores: entry.followStores, knownType: entry.knownType))
    }
    return nil
  }
  
  mutating
  func visitUse(operand: Operand, path: SmallProjectionPath, kind: WalkerVisitKind, state: State) -> State {
    // The visitFunctions don't need to know the `kind` of visit so we can
    // first perform the visit and then continue if necessary. This simplifies the
    // logic a bit.
    let state = visitFunctions.visitUse(operand: operand, path: path, state: state)
    
    if kind == .terminalValue && state.result == .continueWalk {
      let instruction = operand.instruction
      switch instruction {
        // MARK: (operand: non-address) -> (result: address) mode change
      case let rta as RefTailAddrInst:
        if let newPath = pop(.tailElements, from: path, yielding: rta) {
          return walkDown(address: rta, path: newPath, state: state.with(knownType: nil))
        }
      case let rea as RefElementAddrInst:
        if let newPath = pop(.classField, index: rea.fieldIndex, from: path, yielding: rea) {
          return walkDown(address: rea, path: newPath, state: state.with(knownType: nil))
        }
      case let pb as ProjectBoxInst:
        if let newPath = pop(.classField, index: pb.fieldIndex, from: path, yielding: pb) {
          return walkDown(address: pb, path: newPath, state: state.with(knownType: nil))
        }
        // MARK: destruction instructions
      case is StoreInst, is StoreWeakInst, is StoreUnownedInst:
        let store = instruction as! StoringInstruction
        if operand == store.sourceOperand {
          return walkUp(address: store.destination, path: path, state: state)
        } else {
          assert(operand == store.destinationOperand)
          if let si = store as? StoreInst, si.destinationOwnership == .assign {
            if handleDestroy(of: operand.value, path: path, followStores: state.followStores, knownType: nil) {
              return state.with(result: .abortWalk)
            }
          }
          if state.followStores {
            return walkUp(value: store.source, path: path, state: state)
          }
        }
      case let copyAddr as CopyAddrInst:
        if canIgnoreForLoadOrArgument(path) { return state.with(result: .stopWalk) }
        if operand == copyAddr.sourceOperand {
          return walkUp(address: copyAddr.destination, path: path, state: state)
        } else {
          if !copyAddr.isInitializationOfDest {
            if handleDestroy(of: operand.value, path: path, followStores: state.followStores, knownType: nil) {
              return state.with(result: .abortWalk)
            }
          }
          
          if state.followStores {
            assert(operand == copyAddr.destinationOperand)
            return walkUp(value: copyAddr.source, path: path, state: state)
          }
        }
      case is DestroyValueInst, is ReleaseValueInst, is StrongReleaseInst, is DestroyAddrInst:
        if handleDestroy(of: operand.value, path: path, followStores: state.followStores, knownType: state.knownType) {
          return state.with(result: .abortWalk)
        }
      case is ReturnInst:
        return state.with(result: .abortWalk)
      case is ApplyInst, is TryApplyInst, is BeginApplyInst:
        return walkDownCallee(argOp: operand, apply: instruction as! FullApplySite, path: path, state: state)
      case let pai as PartialApplyInst:
        fatalError("TODO")
      case is LoadInst, is LoadWeakInst, is LoadUnownedInst:
        if canIgnoreForLoadOrArgument(path) { return state.with(result: .stopWalk) }
        let svi = instruction as! SingleValueInstruction
        
        // Even when analyzing addresses, a loaded trivial value can be ignored.
        if !svi.type.isNonTrivialOrContainsRawPointer(in: svi.function) { return state.with(result: .stopWalk) }
        
        return walkDown(value: svi, path: path, state: state.with(knownType: nil))
      case let bi as BuiltinInst:
        switch bi.id {
        case .DestroyArray:
          if operand.index != 1 ||
              path.popAllValueFields().popIfMatches(.anyClassField) != nil {
            return state.with(result: .abortWalk)
          }
        default:
          return state.with(result: .abortWalk)
        }
      case is DeallocStackInst, is StrongRetainInst, is RetainValueInst,
        is DebugValueInst, is ValueMetatypeInst, is InjectEnumAddrInst,
        is InitExistentialMetatypeInst, is OpenExistentialMetatypeInst,
        is ExistentialMetatypeInst, is DeallocRefInst, is SetDeallocatingInst,
        is FixLifetimeInst, is ClassifyBridgeObjectInst, is BridgeObjectToWordInst,
        is EndBorrowInst, is EndAccessInst,
        is StrongRetainInst, is RetainValueInst,
        is ClassMethodInst, is SuperMethodInst, is ObjCMethodInst,
        is ObjCSuperMethodInst, is WitnessMethodInst,is DeallocStackRefInst:
        return state.with(result: .stopWalk)
      default:
        return state.with(result: .abortWalk)
      }
    }
    return state
  }
  
  mutating
  func visitDef(object: Value, path: SmallProjectionPath, kind: WalkerVisitKind, state: State) -> State {
    // The visitFunctions don't need to know the `kind` of visit so we can
    // first perform the visit and then continue if necessary. This simplifies the
    // logic a bit.
    let state = visitFunctions.visitDef(def: object, path: path, state: state)
    if state.walkDown {
      if let (path, state) = shouldRecomputeDown(def: object, path: path, state: state.with(walkDown: false)) {
        if object.type.isAddress {
          return walkDown(address: object, path: path, state: state)
        } else {
          return walkDown(value: object, path: path, state: state)
        }
      }
      return state
    }
    
    if kind == .terminalValue && state.result == .continueWalk {
      switch object {
      case is AllocRefInst, is AllocRefDynamicInst:
        if let (path, state) = shouldRecomputeDown(def: object, path: path, state: state) {
          return walkDown(value: object, path: path, state: state)
        }
      case is AllocStackInst, is AllocBoxInst:
        if let (path, state) = shouldRecomputeDown(def: object, path: path, state: state) {
          return walkDown(address: object, path: path, state: state)
        }
      case let arg as FunctionArgument:
        if canIgnoreForLoadOrArgument(path) && arg.isExclusiveIndirectParameter && !state.followStores {
          // TODO: this should be an address right?
          if let (path, state) = shouldRecomputeDown(def: object, path: path, state: state) {
            return walkDown(address: object, path: path, state: state)
          }
        } else {
          return state.with(result: .abortWalk)
        }
      case let arg as BlockArgument:
        fatalError("TODO")
      case let ap as ApplyInst:
        return walkUpApplyResult(apply: ap, path: path, state: state)
      case is LoadInst, is LoadWeakInst, is LoadUnownedInst:
        return walkUp(address: (object as! UnaryInstruction).operand, path: path, state: state.with(followStores: true))
      case let rta as RefTailAddrInst:
        return walkUp(value: rta.operand, path: path.push(.tailElements), state: state)
      case let rea as RefElementAddrInst:
        return walkUp(value: rea.operand, path: path.push(.classField, index: rea.fieldIndex), state: state)
      case let pb as ProjectBoxInst:
        return walkUp(value: pb.operand, path: path.push(.classField, index: pb.fieldIndex), state: state)
      default:
        // MARK: can't recognize origin of value
        return state.with(result: .abortWalk)
      }
    }
    
    return state
  }
  
  
  //===--------------------------------------------------------------------===//
  //                             private state
  //===--------------------------------------------------------------------===//

  private struct CacheEntry {
    private(set) var path = SmallProjectionPath()
    private(set) var followStores = false
    private(set) var knownType: Type?
    private var valid = false

    /// Merge the entry wit a new `path`, `followStores` and `knownType` and
    /// return the resulting entry if a new walk is needed.
    mutating func needWalk(path: SmallProjectionPath, followStores: Bool, knownType: Type?) -> CacheEntry? {
      if !valid {
        // The first time we reach the value: do the walk with `path`, `followStores` and `knownType`.
        valid = true
        self.path = path
        self.followStores = followStores
        self.knownType = knownType
        return self
      }
      // There was already a walk for the value. Merge the `path`, `followStores` and
      // `knownType`.
      var newWalkIsNeeded = false
      if self.path != path {
        let newPath = self.path.merge(with: path)
        if newPath != self.path {
          self.path = newPath
          newWalkIsNeeded = true
        }
      }
      if !self.followStores && followStores {
        self.followStores = true
        newWalkIsNeeded = true
      }
      if let ty = self.knownType, ty != knownType {
        self.knownType = nil
        newWalkIsNeeded = true
      }
      if newWalkIsNeeded {
        // Merging the parameters resulted in something new (more conservative): a new walk is needed.
        return self
      }
      // Nothing changed, no new walk is necessary.
      return nil
    }
  }

  // The caches are not only useful for performance, but are need to avoid infinite
  // recursions of walkUp-walkDown cycles.
  private var walkedDownCache = Dictionary<HashableValue, CacheEntry>()
  private var walkedUpCache = Dictionary<HashableValue, CacheEntry>()

  /// Differences when analyzing address-escapes (instead of value-escapes):
  /// * also addresses with trivial types are tracked
  /// * loads of addresses are ignored
  /// * it can be assumed that addresses cannot escape a function (e.g. indirect parameters)
  private var analyzeAddresses = false

  private let calleeAnalysis: CalleeAnalysis
  
  //===--------------------------------------------------------------------===//
  //                          private utility functions
  //===--------------------------------------------------------------------===//

  private mutating func start(forAnalyzingAddresses: Bool) {
    precondition(walkedDownCache.isEmpty && walkedUpCache.isEmpty)
    analyzeAddresses = forAnalyzingAddresses
  }

  private mutating func cleanup() {
    walkedDownCache.removeAll(keepingCapacity: true)
    walkedUpCache.removeAll(keepingCapacity: true)
  }

  /// Returns true if the type of `value` at `path` is relevant and should be tracked.
  private func hasRelevantType(_ value: Value, at path: SmallProjectionPath) -> Bool {
    let type = value.type
    if type.isNonTrivialOrContainsRawPointer(in: value.function) { return true }
    
    // For selected addresses we also need to consider trivial types (`value`
    // is a selected address if the path does not contain any class projections).
    if analyzeAddresses && type.isAddress && !path.hasClassProjection { return true }
    return false
  }

  /// Returns true if the selected address/value at `path` can be ignored for loading from
  /// that address or for passing that address/value to a called function.
  ///
  /// Passing the selected address (or a value loaded from the selected address) directly
  /// to a function, cannot let the selected address escape:
  ///  * if it's passed as address: indirect parameters cannot escape a function
  ///  * a load from the address does not let the address escape
  ///
  /// Example (continued from the previous example):
  ///    apply %other_func1(%selected_addr)    // cannot let %selected_addr escape (path == v**)
  ///    %l = load %selected_addr
  ///    apply %other_func2(%l)                // cannot let %selected_addr escape (path == v**)
  ///    apply %other_func3(%ref)              // can let %selected_addr escape!   (path == c*.v**)
  ///
  /// Also, we can ignore loads from the selected address, because a loaded value does not
  /// let the address escape.
  private func canIgnoreForLoadOrArgument(_ path: SmallProjectionPath) -> Bool {
    return analyzeAddresses && path.hasNoClassProjection
  }

  /// Tries to pop the given projection from path, if the projected `value` has a relevant type.
  private func pop(_ kind: SmallProjectionPath.FieldKind, index: Int? = nil, from path: SmallProjectionPath, yielding value: Value) -> SmallProjectionPath? {
    if let newPath = path.popIfMatches(kind, index: index),
       hasRelevantType(value, at: newPath) {
      return newPath
    }
    return nil
  }

  // Set a breakpoint here to debug when a value is escaping.
  private var isEscaping: Bool {
    true
  }
  
  private func handleDestroy(of value: Value, path: SmallProjectionPath, followStores: Bool, knownType: Type?) -> Bool {

    // Even if this is a destroy_value of a struct/tuple/enum, the called destructor(s) only take a
    // single class reference as parameter.
    let p = path.popAllValueFields()

    if p.isEmpty {
      // The object to destroy (= the argument of the destructor) cannot escape itself.
      return false
    }
    if analyzeAddresses && p.matches(pattern: SmallProjectionPath(.anyValueFields).push(.anyClassField)) {
      // Any address of a class property of the object to destroy cannot esacpe the destructor.
      // (Whereas a value stored in such a property could escape.)
      return false
    }

    if followStores {
      return isEscaping
    }
    if let exactTy = knownType {
      guard let destructor = calleeAnalysis.getDestructor(ofExactType: exactTy) else {
        return isEscaping
      }
      if destructor.effects.canEscape(argumentIndex: 0, path: p, analyzeAddresses: analyzeAddresses) {
        return isEscaping
      }
    } else {
      // We don't know the exact type, so get all possible called destructure from
      // the callee analysis.
      guard let destructors = calleeAnalysis.getDestructors(of: value.type) else {
        return isEscaping
      }
      for destructor in destructors {
        if destructor.effects.canEscape(argumentIndex: 0, path: p, analyzeAddresses: analyzeAddresses) {
          return isEscaping
        }
      }
    }
    return false
  }

  /// Handle an apply (full or partial) during the walk-down.
  private mutating
  func walkDownCallee(argOp: Operand, apply: ApplySite,
                      path: SmallProjectionPath, state: State) -> State {
    guard let argIdx = apply.argumentIndex(of: argOp) else {
      // The callee or a type dependent operand of the apply does not let escape anything.
      return state
    }

    if canIgnoreForLoadOrArgument(path) { return state }

    // Argument effects do not consider any potential stores to the argument (or it's content).
    // Therefore, if we need to track stores, the argument effects do not correctly describe what we need.
    // For example, argument 0 in the following function is marked as not-escaping, although there
    // is a store to the argument:
    //
    //   sil [escapes !%0.**] @callee(@inout X, @owned X) -> () {
    //   bb0(%0 : $*X, %1 : $X):
    //     store %1 to %0 : $*X
    //   }
    if state.followStores { return state.with(result: .abortWalk) }

    guard let callees = calleeAnalysis.getCallees(callee: apply.callee) else {
      // The callees are not know, e.g. if the callee is a closure, class method, etc.
      return state.with(result: .abortWalk)
    }

    let calleeArgIdx = apply.calleeArgIndex(callerArgIndex: argIdx)

    for callee in callees {
      let effects = callee.effects
      if !effects.canEscape(argumentIndex: calleeArgIdx, path: path, analyzeAddresses: analyzeAddresses) {
        continue
      }
      let walkState = walkDownArgument(calleeArgIdx: calleeArgIdx, argPath: path, state: state,
                          apply: apply, effects: effects)
      if walkState.result == .abortWalk {
        return walkState
      }
    }
    return state
  }

  /// Handle `.escaping` effects for an apply argument during the walk-down.
  private mutating
  func walkDownArgument(calleeArgIdx: Int, argPath: SmallProjectionPath, state: State,
                        apply: ApplySite, effects: FunctionEffects) -> State {
    var matched = false
    for effect in effects.argumentEffects {
      guard case .escaping(let to, let exclusive) = effect.kind else {
        continue
      }
      if effect.selectedArg.matches(.argument(calleeArgIdx), argPath) {
        matched = true

        switch to.value {
        case .returnValue:
          guard let fas = apply as? FullApplySite, let result = fas.singleDirectResult else { return state.with(result: .abortWalk) }

          let state = exclusive ? state.with(followStores: false) : state.with(followStores: false).with(knownType: nil)
          let walkState: State
          if result.type.isAddress {
            walkState = walkDown(address: result, path: to.pathPattern, state: state)
          } else {
            walkState = walkDown(value: result, path: to.pathPattern, state: state)
          }
          
          if walkState.result == .abortWalk {
            return walkState
          }
        case .argument(let toArgIdx):
          guard let callerToIdx = apply.callerArgIndex(calleeArgIndex: toArgIdx) else {
            return state.with(result: .abortWalk)
          }

          // Continue at the destination of an arg-to-arg escape.
          let arg = apply.arguments[callerToIdx]
          let walkState: State
          
          if arg.type.isAddress {
            walkState = walkUp(address: arg, path: to.pathPattern, state: state.with(followStores: false).with(knownType: nil))
          } else {
            walkState = walkUp(value: arg, path: to.pathPattern, state: state.with(followStores: false).with(knownType: nil))
          }
          if walkState.result == .abortWalk {
            return walkState
          }
        }
        continue
      }
      // Handle the reverse direction of an arg-to-arg escape.
      if to.matches(.argument(calleeArgIdx), argPath) {
        guard let callerArgIdx = apply.callerArgIndex(calleeArgIndex: effect.selectedArg.argumentIndex) else {
          return state.with(result: .abortWalk)
        }
        if !exclusive { return state.with(result: .abortWalk) }

        matched = true
        
        let arg = apply.arguments[calleeArgIdx]
        let walkState: State
        if arg.type.isAddress {
          walkState = walkUp(address: arg, path: effect.selectedArg.pathPattern, state: state.with(followStores: false).with(knownType: nil))
        } else {
          walkState = walkUp(value: arg, path: effect.selectedArg.pathPattern, state: state.with(followStores: false).with(knownType: nil))
        }
        
        if walkState.result == .abortWalk {
          return walkState
        }
        continue
      }
    }
    if !matched { return state.with(result: .abortWalk) }
    return state.with(result: .stopWalk)
  }
  
  /// Walks up from the return to the source argument if there is an "exclusive"
  /// escaping effect on an argument.
  private mutating
  func walkUpApplyResult(apply: FullApplySite,
                         path: SmallProjectionPath, state: State) -> State {
    guard let callees = calleeAnalysis.getCallees(callee: apply.callee) else {
      return state.with(result: .abortWalk)
    }

    for callee in callees {
      var matched = false
      for effect in callee.effects.argumentEffects {
        switch effect.kind {
        case .notEscaping:
          break
        case .escaping(let toSelectedArg, let exclusive):
          if exclusive && toSelectedArg.matches(.returnValue, path) {
            matched = true
            let arg = apply.arguments[effect.selectedArg.argumentIndex]
            
            let walkState: State
            if arg.type.isAddress {
              walkState = walkUp(address: arg, path: effect.selectedArg.pathPattern, state: state.with(knownType: nil))
            } else {
              walkState = walkUp(value: arg, path: effect.selectedArg.pathPattern, state: state.with(knownType: nil))
            }
            if walkState.result == .abortWalk {
              return walkState
            }
          }
        }
      }
      if !matched {
        return state.with(result: .abortWalk)
      }
    }
    return state.with(result: .stopWalk)
  }
}
