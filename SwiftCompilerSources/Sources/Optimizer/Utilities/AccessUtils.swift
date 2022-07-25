import SIL

enum AccessBaseKind {
  case Box
  case Stack
  case Global
  case Class
  case Tail
  case Argument
  case Yield
  case Pointer
  
  init?(address: Value) {
    switch address {
    case is ProjectBoxInst:
      self = .Box
    case is AllocStackInst:
      self = .Stack
    case is GlobalAddrInst:
      self = .Global
    case is RefElementAddrInst:
      self = .Class
    case is RefTailAddrInst:
      self = .Tail
    case is FunctionArgument:
      self = .Argument
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
  let baseKind: AccessBaseKind

  init?(baseAddress: Value, baseKind: AccessBaseKind) {
    switch baseKind {
    case .Class     where baseAddress is RefElementAddrInst   : break
    case .Tail      where baseAddress is RefTailAddrInst      : break
    case .Box       where baseAddress is ProjectBoxInst       : break
    case .Stack     where baseAddress is AllocStackInst       : break
    case .Argument  where baseAddress is FunctionArgument     : break
    case .Yield
      where baseAddress.definingInstruction is BeginApplyInst : break
    case .Global:
      switch baseAddress {
        case is GlobalAddrInst: break
        // TODO: other cases?
        default:
          return nil
      }
    case .Pointer:
      switch baseAddress {
        case is PointerToAddressInst: break
        // TODO: other cases?
        default:
          return nil
      }
    default:
      return nil
    }

    self.baseAddress = baseAddress
    self.baseKind = baseKind
  }
  
  var description: String {
    "\(baseKind) - \(baseAddress)"
  }

  var isObjectAccess: Bool {
    return baseKind == .Class || baseKind == .Tail
  }
  
  var referenceWithPathComponent: (ref: Value, comp: (SmallProjectionPath.FieldKind, Int))? {
    switch baseAddress {
    case let rea as RefElementAddrInst:
      return (rea.operand, (.classField, rea.fieldIndex))
    case let pb as ProjectBoxInst:
      return (pb.operand, (.classField, pb.fieldIndex))
    case let rta as RefTailAddrInst:
      return (rta.operand,(.tailElements, 0))
    default:
      return nil
    }
  }
  
  var reference: Value? { referenceWithPathComponent?.ref }
  
  var isLet: Bool {
    switch baseAddress {
    case let rea as RefElementAddrInst:
      return rea.fieldIsLet
    case let ga as GlobalAddrInst:
      return ga.global.isLet
    default:
      return false
    }
  }
  
  var isLocal: Bool {
    switch baseKind {
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
    switch baseKind {
    case .Box:
      return baseAddress is AllocBoxInst
    case .Stack, .Global:
      return true
    case .Argument:
      return (baseAddress as! FunctionArgument).isExclusiveIndirectParameter
    case .Class, .Tail, .Yield, .Pointer:
      return false
    }
  }
  
  func isDistinct(from other: AccessBase) -> Bool {
    if self.isUniquelyIdentified {
      if other.isUniquelyIdentified {
        if baseKind != other.baseKind { return true }
        switch baseKind {
        case .Global:
          return (baseAddress as! GlobalAddrInst).global != (other.baseAddress as! GlobalAddrInst).global
        case .Class: 
          return (baseAddress as! RefElementAddrInst).fieldIndex != (other.baseAddress as! RefElementAddrInst).fieldIndex
        case .Box, .Stack, .Argument, .Tail, .Yield, .Pointer:
          return false
        }
      }
    }
    if other.isUniquelyIdentified { return other.isDistinct(from: self) }

    if isObjectAccess {
      if other.isObjectAccess {
        if baseKind != other.baseKind { return true }

        return baseKind == .Class &&
               (baseAddress as! RefElementAddrInst).fieldIndex != (other.baseAddress as! RefElementAddrInst).fieldIndex
      }

      return false
    }

    if other.isObjectAccess {
      return other.isDistinct(from: self)
    }

    return false
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
  
  func isDistinct(from other: AccessPath) -> Bool {
    if base.isDistinct(from: other.base) { return true }
    return false
  }
}

/// An `AccessStoragePath` is the reference (or a value for which the
/// reference is a stored property) an address originates from.
struct AccessStoragePath {
  let storage: Value
  
  /// Only valid paths are: `"<sequence of value projections>.<one reference projection>.<sequence of address projections>"`
  let path: SmallProjectionPath
}

typealias AccessStorage = (maybeRoot: AccessStoragePath?, base: AccessBase)

enum EnclosingScope {
  case scope(BeginAccessInst)
  case base(AccessBase)
}


func canBeOperandOfIndexAddr(_ value: Value) -> Bool {
  switch value {
  case is IndexAddrInst, is RefTailAddrInst:
    return true
  default:
    return false
  }
}

fileprivate struct PointerIdentificationUseDefWalkerInternal : ValueUseDefWalker {
  var addrType: Type!
  var result: Value?

  mutating func rootDef(value: Value, path: SmallProjectionPath) -> WalkResult {
    self.result = nil
    return .abortWalk
  }

  mutating func walkUp(value: Value, path: SmallProjectionPath) -> WalkResult {
    switch value {
    case is FunctionArgument:
      self.result = value
      return .continueWalk
    case let atp as AddressToPointerInst:
      if let result = result, atp.operand != result {
        self.result = nil
        return .abortWalk
      }
      // TODO: instead of checking type equality perhaps check
      //       layout compatibility, if possible?
      if addrType == atp.operand.type, path.isEmpty {
        self.result = atp.operand
        return .continueWalk
      }
    case is BlockArgument, is MarkDependenceInst, is CopyValueInst,
         is StructExtractInst, is TupleExtractInst, is StructInst, is TupleInst:
      return walkUpDefault(value: value, path: path)
    default:
      break
    }

    self.result = nil
    return .abortWalk
  }

  var walkUpCache = WalkerCache<Path>()
}

struct PointerIdentificationWalker {
  private var walker = PointerIdentificationUseDefWalkerInternal()

  mutating func compute(_ atp: PointerToAddressInst) -> Value? {
    walker.addrType = atp.type
    walker.result = nil
    _ = walker.walkUp(value: atp.operand, path: SmallProjectionPath())
    return walker.result
  }
}

fileprivate struct AccessPathWalkerInternal : AddressUseDefWalker {  
  var result: AccessPath? = nil
  private var _beginAccess: BeginAccessInst? = nil
  var scope: EnclosingScope? {
    if let ba = _beginAccess {
      return .scope(ba)
    } else {
      guard let accessPath = result else { return nil }
      return .base(accessPath.base)
    }
  }

  private var pointerWalker = PointerIdentificationWalker()
  
  mutating func start() {
    result = nil
    _beginAccess = nil
  }

  struct Path : SimpleWalkingPath {
    let projectionPath: SmallProjectionPath

    // Tracks whether an `index_addr` instruction was crossed.
    // It should be (FIXME: check if it's enforced) that operands
    // of `index_addr` must be `tail_addr` or other `index_addr` results.
    let indexAddr: Bool

    func with(projectionPath: SmallProjectionPath) -> Self {
      return Self(projectionPath: projectionPath, indexAddr: indexAddr)
    }

    func with(indexAddr: Bool) -> Self {
      return Self(projectionPath: projectionPath, indexAddr: indexAddr)
    }

    func merge(with other: Self) -> Self {
      return Self(
        projectionPath: projectionPath.merge(with: other.projectionPath),
        indexAddr: indexAddr || other.indexAddr
      )
    }
  }
  
  mutating func rootDef(address: Value, path: Path) -> WalkResult {
    
    func answer(_ kind: AccessBaseKind?) -> WalkResult {
      if let kind = kind {
        self.result =  AccessPath(
          base: AccessBase(baseAddress: address, baseKind: kind)!,
          projectionPath: path.projectionPath
        )
        return .continueWalk
      } else {
        self.result = nil
        return .abortWalk
      }
    }

    // Try identifying the address a pointer originates from
    if let p2ai = address as? PointerToAddressInst,
       let newAddress = pointerWalker.compute(p2ai) {
      return walkUp(address: newAddress, path: path)
    }
    
    let maybeKind = AccessBaseKind(address: address)
    
    // If this is a base then we're done
    if let kind = maybeKind {
      return answer(kind)
    }
    
    if address.definingInstruction is BeginApplyInst {
      return answer(.Yield)
    }
    
    // The base is unidentified
    return answer(nil)
  }
  
  mutating func walkUp(address: Value, path: Path) -> WalkResult {
    if address is IndexAddrInst {
      // Track that we crossed an `index_addr` during the walk-up
      return walkUpDefault(address: address, path: path.with(indexAddr: true))
    } else if path.indexAddr && !canBeOperandOfIndexAddr(address) {
      // An `index_addr` instruction cannot be derived from an address
      // projection. Bail out
      self.result = nil
      return .abortWalk
    } else if let ba = address as? BeginAccessInst, _beginAccess == nil {
      _beginAccess = ba
    }
    return walkUpDefault(address: address, path: path.with(indexAddr: false))
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
    _ = walker.walkUp(
      address: address,
      path: AccessPathWalkerInternal.Path(projectionPath: SmallProjectionPath(), indexAddr: false)
    )
    
    return walker.result
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

struct AccessStoragePathWalkerInternal : ValueUseDefWalker {
  var walkUpCache = WalkerCache<Path>()
  var origins: [AccessStoragePath] = []

  mutating func start() {
    walkUpCache.clear()
    origins.removeAll(keepingCapacity: true)
  }
  
  // NOTE: the storage can also be provided by a LoadInst
  mutating func rootDef(value: Value, path: SmallProjectionPath) -> WalkResult {
    origins.append(AccessStoragePath(storage: value, path: path))
    return .continueWalk
  }
}

struct AccessStoragePathWalker {
  private var walker = AccessStoragePathWalkerInternal()
  mutating func compute(_ ap: AccessPath) -> [AccessStoragePath] {
    walker.start()
    if let (ref, (fieldKind, fieldIndex)) = ap.base.referenceWithPathComponent {
      _ = walker.walkUp(value: ref, path: ap.projectionPath.push(fieldKind, index: fieldIndex))
      return walker.origins
    } else {
      return [AccessStoragePath(storage: ap.base.baseAddress, path: ap.projectionPath)]
    }
  }
  
  // TODO: assert that argument is actually a reference (?)
  mutating func compute(_ ref: Value) -> [AccessStoragePath] {
    walker.start()
    _ = walker.walkUp(value: ref, path: SmallProjectionPath())
    return walker.origins
  }
}

