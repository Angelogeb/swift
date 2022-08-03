import SIL

public enum AccessBaseKind {
  case box
  case stack
  case global
  case `class`
  case tail
  case argument
  case yield
  case pointer

  var isObject: Bool { self == .class || self == .tail }
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

  init?(baseAddress: Value) {
    switch baseAddress {
    case is RefElementAddrInst   : baseKind = .class
    case is RefTailAddrInst      : baseKind = .tail
    case is ProjectBoxInst       : baseKind = .box
    case is AllocStackInst       : baseKind = .stack
    case is FunctionArgument     : baseKind = .argument
    case is GlobalAddrInst       : baseKind = .global
    default:
      if baseAddress.definingInstruction is BeginApplyInst &&
         baseAddress.type.isAddress {
        baseKind = .yield
      } else {
        return nil
      }
    // case .Pointer:
    //   switch baseAddress {
    //     case is PointerToAddressInst: break
    //     // TODO: other cases?
    //     default:
    //       return nil
    //   }
    // default:
    //   return nil
    }

    self.baseAddress = baseAddress
  }

  init(baseAddress: Value, baseKind: AccessBaseKind) {
    self.baseAddress = baseAddress
    self.baseKind = baseKind
  }

  var description: String {
    "\(baseKind) - \(baseAddress)"
  }

  var isObjectAccess: Bool {
    return baseKind == .class || baseKind == .tail
  }

  // If this `AccessBase` is obtained froma a reference type,
  // results in the reference `ref` and a `component` describing
  // the projection type (tail or class field) and the corresponding field index
  var referenceWithPathComponent: (ref: Value, component: (SmallProjectionPath.FieldKind, Int))? {
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

  /// Returns `true` if the address is immediately produced by a stack or box allocation
  var isLocal: Bool {
    switch baseKind {
    case .box:
      // The operand of the projection can be an argument, in which
      // case it wouldn't be local
      return (baseAddress as! ProjectBoxInst).operand is AllocBoxInst
    case .stack:
      return true
    default:
      return false
    }
  }

  /// Returns `true` if we can reliably compare for equality this `AccessBase`
  /// with another `AccessBase`.
  /// When comparing two uniquely identified access bases, it can be followed that if they are not equal,
  /// also the accessed memory addresses do not alias.
  /// This is e.g. not the case for class references: two different references may still point to the same object.
  var isUniquelyIdentified: Bool {
    switch baseKind {
    case .box:
      // The operand `%op` in `%baseAddress = project_box %op` can
      // be `alloc_box` or an argument. Only if it's a fresh allocation it is
      // uniquelyIdentified, otherwise it is aliasable, as all the other references.
      return baseAddress is AllocBoxInst
    case .stack, .global:
      return true
    case .argument:
      // An argument address that is non-aliasable
      return (baseAddress as! FunctionArgument).isExclusiveIndirectParameter
    case .class, .tail, .yield, .pointer:
      // References (.class and .tail) may alias, and so do pointers and
      // yield results
      return false
    }
  }

  /// Returns `true` if the two access bases do not alias
  func isDistinct(from other: AccessBase) -> Bool {
    switch (baseAddress, other.baseAddress) {
    case is (AllocStackInst, AllocStackInst),
         is (AllocBoxInst, AllocBoxInst):
      return baseAddress != other.baseAddress
    case let (this as GlobalAddrInst, that as GlobalAddrInst):
      return this.global != that.global
    case let (this as FunctionArgument, that as FunctionArgument):
      return (this.isExclusiveIndirectParameter || that.isExclusiveIndirectParameter) && this != that
    case let (this as RefElementAddrInst, that as RefElementAddrInst):
      return (this.fieldIndex != that.fieldIndex)
    default:
      if isUniquelyIdentified && other.isUniquelyIdentified && baseKind != other.baseKind { return true }
      // property: `isUniquelyIdentified` XOR `isObject`
      if isUniquelyIdentified && other.baseKind.isObject { return true }
      if baseKind.isObject && other.isUniquelyIdentified { return true }
      return false
    }
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
    return base.isDistinct(from: other.base) ||
      (base.baseAddress == other.base.baseAddress && projectionPath != other.projectionPath)
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

/// Given a `%addr = pointer_to_address %ptr_operand` instruction tries to identify
/// the address the pointer operand `ptr_operand` originates from, if any exists.
/// This is useful to identify patterns like
/// ```
/// %orig_addr = global_addr @...
/// %ptr = address_to_pointer %orig_addr
/// %addr = pointer_to_address %ptr
/// ```
/// which might arise when `[global_init]` functions for global addressors are inlined.
///
/// Alternatively, if the pointer originates from a ``FunctionArgument``, the argument is returned.
///
/// This underlying use-def traversal might cross phi arguments to identify the originating address
/// to handle diamond-shaped control-flow with common originating address which might arise due to transformations ([example] (https://github.com/apple/swift/blob/8f9c5339542b17af9033f51ad7a0b95a043cad1b/test/SILOptimizer/access_storage_analysis_ossa.sil#L669-L705)) .
struct PointerIdentification {
  private var walker = PointerIdentificationUseDefWalker()

  typealias AddressOrPointerArgument = Value
  mutating func getOriginatingAddressOrArgument(_ atp: PointerToAddressInst) -> AddressOrPointerArgument? {
    walker.start(atp.type)
    if walker.walkUp(value: atp.operand, path: SmallProjectionPath()) == .abortWalk {
      return nil
    }
    return walker.result
  }

  private struct PointerIdentificationUseDefWalker : ValueUseDefWalker {
    private var addrType: Type!
    private(set) var result: Value?

    mutating func start(_ addrType: Type) {
      self.addrType = addrType
      result = nil
      walkUpCache.clear()
    }

    mutating func rootDef(value: Value, path: SmallProjectionPath) -> WalkResult {
      switch value {
      case is FunctionArgument:
        self.result = value
        return .continueWalk
      case let atp as AddressToPointerInst:
        if let result = result, atp.operand != result {
          self.result = nil
          return .abortWalk
        }

        if addrType == atp.operand.type, path.isEmpty {
          self.result = atp.operand
          return .continueWalk
        }
      default:
        break
      }
      self.result = nil
      return .abortWalk
    }

    mutating func walkUp(value: Value, path: SmallProjectionPath) -> WalkResult {
      switch value {
      case is BlockArgument, is MarkDependenceInst, is CopyValueInst,
           is StructExtractInst, is TupleExtractInst, is StructInst, is TupleInst,
           is FunctionArgument, is AddressToPointerInst:
        return walkUpDefault(value: value, path: path)
      default:
        self.result = nil
        return .abortWalk
      }
    }

    var walkUpCache = WalkerCache<Path>()
  }
}


/// A walker utility that given an address definition computes the `AccessPath`
/// of the access (the base address and the address projections to the accessed fields) and
/// the innermost enclosing scope (`begin_access`).
struct AccessPathWalker {
  private var walker = AccessPathWalker()
  mutating func getAccessPath(of address: Value) -> AccessPath? {
    assert(address.type.isAddress, "Expected address")
    walker.start()
    if walker.walkUp(address: address, path: AccessPathWalker.Path()) == .abortWalk {
      return nil
    }
    return walker.result
  }

  mutating func getAccessPathWithScope(of address: Value) -> (AccessPath?, EnclosingScope?) {
    let ap = getAccessPath(of: address)
    return (ap, walker.scope)
  }

  mutating func getAccessBase(of address: Value) -> AccessBase? {
    getAccessPath(of: address)?.base
  }

  mutating func getAccessScope(of address: Value) -> EnclosingScope? {
    getAccessPathWithScope(of: address).1
  }

  private struct AccessPathWalker : AddressUseDefWalker {
    private(set) var result: AccessPath? = nil
    private var foundBeginAccess: BeginAccessInst? = nil
    var scope: EnclosingScope? {
      if let ba = foundBeginAccess {
        return .scope(ba)
      } else {
        guard let accessPath = result else { return nil }
        return .base(accessPath.base)
      }
    }

    private var pointerId = PointerIdentification()

    mutating func start() {
      result = nil
      foundBeginAccess = nil
    }

    struct Path : SimpleWalkingPath {
      let projectionPath: SmallProjectionPath

      // Tracks whether an `index_addr` instruction was crossed.
      // It should be (FIXME: check if it's enforced) that operands
      // of `index_addr` must be `tail_addr` or other `index_addr` results.
      let indexAddr: Bool

      init(projectionPath: SmallProjectionPath = SmallProjectionPath(), indexAddr: Bool = false) {
        self.projectionPath = projectionPath
        self.indexAddr = indexAddr
      }

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
      // Try identifying the address a pointer originates from
      if let p2ai = address as? PointerToAddressInst,
         let newAddress = pointerId.getOriginatingAddressOrArgument(p2ai) {
        return walkUp(address: newAddress, path: path)
      }

      // If this is a base then we're done
      if let base = AccessBase(baseAddress: address) {
        self.result = AccessPath(base: base, projectionPath: path.projectionPath)
        return .continueWalk
      }

      // The base is unidentified
      self.result = nil
      return .abortWalk
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
      } else if let ba = address as? BeginAccessInst, foundBeginAccess == nil {
        foundBeginAccess = ba
      }
      return walkUpDefault(address: address, path: path.with(indexAddr: false))
    }
  }
}

struct AccessStoragePathWalker {
  private var walker = AccessStoragePathWalker()
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

  private struct AccessStoragePathWalker : ValueUseDefWalker {
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
}

