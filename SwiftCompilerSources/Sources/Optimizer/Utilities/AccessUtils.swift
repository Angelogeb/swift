import SIL

enum AccessStorageKind {
  case Box
  case Stack
  case Global
  case Class
  case Tail
  case Argument
  case Yield
  case Nested
  case Pointer
  
  static func of(address: Value) -> AccessStorageKind? {
    switch address {
    case is ProjectBoxInst:
      return .Box
    case is AllocStackInst:
      return .Stack
    case is GlobalAddrInst:
      return .Global
    case is RefElementAddrInst:
      return .Class
    case is RefTailAddrInst:
      return .Tail
    case is FunctionArgument:
      return .Argument
    case is BeginAccessInst:
      return .Nested
    default:
      // BeginApplyInst       -> .Yield   must be handled by client
      // AddressToPointerInst -> .Pointer must be handled by client
      return nil
    }
  }
}


/// The base of an access is the instruction that produced the base address
/// of the accessing instruction (`store`/`load`). Usually such instruction produces a base address taking
/// as operand nothing (`alloc_stack`, `global_addr`) or a value (`ref_element_addr`, `ref_tail_addr`).
/// The access isn't necessarily on the base and instead can be to an "offset address"
/// from the base produced through a sequence of `struct_element_addr`/`index_addr`.
/// ```
/// %base1 = ref_element_addr %ref
/// %base2 = alloc_stack $S
/// %base3 = global_addr @gaddr
/// %addr1 = struct_element_addr %base1
/// %access1 = store %v1 to [trivial] %addr1   // accessed address is offset from base
/// %access2 = store %v2 to [trivial] %base2   // accessed address is base itself
/// ```
/// The base address is never inside an access scope.
struct AccessBase : CustomStringConvertible {
  let baseAddress: Value
  let storageKind: AccessStorageKind
  
  var description: String {
    "\(storageKind) - \(baseAddress)"
  }
  
  var referenceWithPathComponent: (ref: Value, comp: (SmallProjectionPath.FieldKind, Int))? {
    switch storageKind {
    case .Box, .Tail, .Class:
      switch baseAddress {
      case let rea as RefElementAddrInst:
        return (rea.operand, (.classField, rea.fieldIndex))
      case let pb as ProjectBoxInst:
        return (pb.operand, (.classField, pb.fieldIndex))
      case let rta as RefTailAddrInst:
        return (rta.operand,(.tailElements, 0))
      default:
        fatalError("Inconsistent state")
      }
    default:
      return nil
    }
  }
  
  var reference: Value? { referenceWithPathComponent?.ref }
  
  var isLet: Bool {
    switch baseAddress {
    case is RefElementAddrInst:
      fatalError() // FIXME: add support for looking up types in libswift etc
    default:
      fatalError()
    }
  }
  
  var isLocal: Bool {
    switch storageKind {
    case .Box:
      return baseAddress is AllocBoxInst
    case .Stack:
      return true
    default:
      return false
    }
  }
  
  /// Returns `true` if we can reliably compare for equality this `AccessBase`
  /// with another `AccessBase`
  var isUniquelyIdentified: Bool {
    switch storageKind {
    case .Box:
      return baseAddress is AllocBoxInst
    case .Stack, .Global:
      return true
    case .Argument:
      return (baseAddress as! FunctionArgument).isExclusiveIndirectParameter
    default:
      return false
    }
  }
  
  func isDistinct(from other: AccessBase) -> Bool {
    fatalError()
  }
}

/// An `AccessPath` is a pair of a `base: AccessBase` and a `projectionPath: Path`
/// which denotes the offset of the access from the base in terms of projections.
struct AccessPath : CustomStringConvertible {
  var base: AccessBase

  /// address projections only
  var projectionPath: SmallProjectionPath
  
  var description: String {
    "\(projectionPath): \(base)"
  }
  
  func isDistinct(from: AccessPath) -> Bool {
    fatalError("TODO")
  }
}

/// An `AccessRoot` is the reference (or a value for which the
/// reference is a stored property) an address originates from.
struct AccessRoot {
  var root: Value
  
  /// Only valid paths are: `"<sequence of value projections>.<one reference projection>.<sequence of address projections>"`
  var path: SmallProjectionPath
}

typealias AccessStorage = (maybeRoot: AccessRoot?, base: AccessBase)

/// An `AccessScope` denotes a pair of `begin_access` `end_access`
/// instructions.
struct AccessScope {
  // TODO: add support for begin_access_unpaired
  var beginAccess: BeginAccessInst

  var accessedAddress: Value { beginAccess.operand }

  var accessKind: AccessKind { beginAccess.accessKind }
  
  var scopeEndingInstructions: EndAccessInstructions {
    beginAccess.endAccesses
  }
}

enum EnclosingScope {
  case scope(AccessScope)
  case base(AccessBase)
}


func canBeOperandOfIndexAddr(_ value: Value) -> Bool {
  switch value {
  case is IndexAddrInst, is PointerToAddressInst, is RefTailAddrInst:
    return true
  default:
    return false
  }
}


protocol HasMerge {
  init()
  mutating func merge(with: Self) -> Self?
}

struct CacheEntry<State : HasMerge> {
  typealias Path = SmallProjectionPath
  var valid: Bool = false
  var state: State = State()
  var path: Path = Path()
  
  mutating func needWalk(path: Path, state: State) -> CacheEntry? {
    if !valid {
      valid = true
      self.state = state
      self.path = path
      return self
    }
    let newPath = self.path.merge(with: path)
    let newState = self.state.merge(with: state)
    if newPath != self.path || newState != nil {
      return self
    }
    
    return nil
  }
}

protocol WithDefaultCache where Self : ValueUseDefWalker, Self.State : HasMerge {
  typealias DefaultCache = Dictionary<HashableValue, CacheEntry<State>>
  var walkUpCache: DefaultCache { get set }
}

extension WithDefaultCache {
  
  mutating func shouldRecomputeUp(def: Value, path: Path, state: State) -> (Path, State)? {
    if let entry = walkUpCache[def.hashable, default: CacheEntry()].needWalk(path: path, state: state) {
      return (entry.path, entry.state)
    }
    return nil
  }
}

fileprivate struct AccessPathWalkerInternal : AddressUseDefWalker, ValueUseDefWalker, WithDefaultCache {
  typealias ResultBase = (
    base: Value,
    kind: AccessStorageKind,
    path: Path
  )?
  
  var result: ResultBase = nil
  private var _beginAccess: BeginAccessInst? = nil
  var scope: EnclosingScope? {
    if let ba = _beginAccess {
      return .scope(AccessScope(beginAccess: ba))
    } else {
      guard let (base, kind, _) = result else { return nil /*TODO: doublecheck*/ }
      return .base(AccessBase(baseAddress: base, storageKind: kind))
    }
  }
  
  var walkUpCache = DefaultCache(minimumCapacity: 64)
  
  mutating func start() {
    result = nil
    _beginAccess = nil
    walkUpCache.removeAll(keepingCapacity: true)
  }
  
  struct State : HasMerge {
    var cast: Value?
    // Tracks whether an `index_addr` instruction was crossed.
    // It should be (FIXME: check if it's enforced) that operands
    // of `index_addr` must be `tail_addr` or other `index_addr` results.
    var indexAddr: Bool = false
    
    mutating func merge(with other: Self) -> Self? {
      if indexAddr != other.indexAddr {
        indexAddr = indexAddr || other.indexAddr
        return self
      }
      return nil
    }
  }
  
  mutating func rootDef(address: Value, path: Path, state: State) -> WalkResult {
    
    func answer(_ kind: AccessStorageKind?) -> WalkResult {
      if let kind = kind {
        self.result = (address, kind, path)
        return .continueWalk
      } else {
        self.result = nil
        return .abortWalk
      }
    }
    
    let maybeKind = AccessStorageKind.of(address: address)
    
    if let currentBase = result, /* Another `rootDef` has found a base as well */
       let kind = maybeKind      /* and this is also a base                    */{
      // If it's different then the base cannot be identified
      if currentBase.base != address || currentBase.kind != kind || currentBase.path != path {
        return answer(nil)
      }
      // Otherwise the base is still the same
      return .continueWalk
    }
    
    // If this is a base then we're done
    if let kind = maybeKind, kind != .Nested /* For `begin_access` we let the walk continue */ {
      return answer(kind)
    }
    
    if address.definingInstruction is BeginApplyInst {
      return answer(.Yield)
    }
    
     if let ptoa = address as? PointerToAddressInst {
       // Try finding the base of the pointer, remembering the cast as state
       return walkUp(value: ptoa.operand, path: path, state: State(cast: ptoa, indexAddr: false))
     }
    
    // The base is unidentified
    return answer(nil)
  }
  
  mutating func walkUp(address: Value, path: Path, state: State) -> WalkResult {
    if address is IndexAddrInst {
      // Track that we crossed an `index_addr` during the walk-up
      return walkUpDefault(address: address, path: path, state: State(cast: state.cast, indexAddr: true))
    } else if state.indexAddr && !canBeOperandOfIndexAddr(address) {
      // An `index_addr` instruction cannot be derived from an address
      // projection. Bail out
      self.result = nil
      return .abortWalk
    } else if let ba = address as? BeginAccessInst, _beginAccess == nil {
      _beginAccess = ba
    }
    return walkUpDefault(address: address, path: path, state: State(cast: state.cast, indexAddr: false))
  }
  
  mutating func rootDef(value: Value, path: Path, state: State) -> WalkResult { fatalError("Unreachable") }
  
  mutating func walkUp(value: Value, path: Path, state: State) -> WalkResult {
    assert(state.cast != nil, "A value walkUp was requested but no cast provided as state")
    switch value {
    case is FunctionArgument:
      // TODO: maybe define `walkUp(value:` to track certain crossed
      // instructions like `RefToBridgeObjectInst` (?)
      self.result = (value, .Pointer, path)
      return .continueWalk
    case let atp as AddressToPointerInst:
      if let cast = state.cast, cast.type == atp.operand.type {
        return walkUp(address: atp.operand, path: path, state: State(cast: nil, indexAddr: false))
      }
    case let arg as BlockArgument:
      return walkUpDefault(value: arg, path: path, state: state)
    default:
      break
    }
    
    self.result = nil
    return .abortWalk
  }
}

/// A walker utility that given an address definition computes the `AccessPath`
/// of the access (the base address and the address projections to the accessed fields) and
/// the innermost enclosing scope (`begin_access`).
struct AccessPathWalker {
  private var walker = AccessPathWalkerInternal()
  mutating func compute(_ address: Value) -> AccessPath? {
    assert(address.type.isAddress, "Expected address")
    walker.start()
    _ = walker.walkUp(address: address, path: AccessPathWalkerInternal.Path(),
                      state: AccessPathWalkerInternal.State(cast: nil, indexAddr: false))
    
    if let (instr, kind, path) = walker.result {
      return AccessPath(base: AccessBase(baseAddress: instr, storageKind: kind), projectionPath: path)
    }
    
    return nil
  }
  
  mutating func pathWithScope(of address: Value) -> (AccessPath?, EnclosingScope?) {
    let ap = compute(address)
    return (ap, walker.scope)
  }
  
  mutating func base(of address: Value) -> AccessBase? {
    compute(address)?.base
  }
  
  mutating func scope(of address: Value) -> EnclosingScope {
    _ = compute(address)
    return walker.scope!
  }
}

struct AccessRootWalkerInternal : ValueUseDefWalker, WithDefaultCache {
  var walkUpCache = DefaultCache(minimumCapacity: 64)
  var roots: [AccessRoot] = []
  
  mutating func start() {
    walkUpCache.removeAll(keepingCapacity: true)
    roots.removeAll(keepingCapacity: true)
  }
  
  struct State : HasMerge {
    mutating func merge(with other: Self) -> Self? { return nil }
  }
  
  mutating func rootDef(value: Value, path: Path, state: State) -> WalkResult {
    roots.append(AccessRoot(root: value, path: path))
    return .continueWalk
  }
  
}

struct AccessRootWalker {
  private var walker = AccessRootWalkerInternal()
  mutating func compute(_ ap: AccessPath) -> [AccessRoot] {
    walker.start()
    if let (ref, (fieldKind, fieldIndex)) = ap.base.referenceWithPathComponent {
      _ = walker.walkUp(value: ref, path: ap.projectionPath.push(fieldKind, index: fieldIndex),
                        state: AccessRootWalkerInternal.State())
    }
    return walker.roots
  }
  
  mutating func compute(_ ref: Value) -> [AccessRoot] {
    walker.start()
    _ = walker.walkUp(value: ref, path: SmallProjectionPath(), state: AccessRootWalkerInternal.State())
    return walker.roots
  }
}


// TODO
struct AccessUseWalker : ValueDefUseWalker, AddressDefUseWalker {
  
  struct State {}
  
  mutating func leafUse(value: Operand, path: Path, state: State) -> WalkResult {
    return .abortWalk
  }
  
  mutating func leafUse(address: Operand, path: Path, state: State) -> WalkResult {
    return .abortWalk
  }
  
  mutating func shouldRecomputeDown(def: Value, path: Path, state: State) -> (Path, State)? {
    return nil
  }
}
