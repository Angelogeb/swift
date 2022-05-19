//===--- WalkUtils.swift - Utilities for use-def def-use walks ------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2022 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

import SIL

public enum WalkCallbackResult {
  /// skip traversal
  case ignore
  /// stop the walk, add the current use/def and path to the result
  case abortWalk
  /// continue the walk
  case continueWalk
}

/// We will use "object" to denote SILValues, which can be either references or addresses
/// We use `%d' <- %u = inst %d` to mean that in a walkup the object used `%d`
/// is "generated" by definition `%d'` where we can reach `%d` as `proj(d', path)`.
/// We use `%d -> %u = inst %d'` to mean that in a walkdown the object defined `%d`
/// is the one that generates the operand `%d'` of the use instruction and we can reach `%d'` as `proj(d, path)`
/// The walk{Down,Up}{Value,Address} will perform a use-def/def-use traversal that
/// 1. stops whenever the flow from operand to result and viceversa changes from address to value and viceversa
///   adding the use/def to the result
/// 2. adds a use/def to the result when the visit{Use,Def} returns `.abortWalk` or when
/// 3. reaching a leaf/root use/def
/// 4. Currently `begin_access` etc. are treated as forwarding uses (walk does not stop unless requested by callback)

public typealias UseCallback = (Operand, SmallProjectionPath) -> WalkCallbackResult
public typealias DefCallback = (Value, SmallProjectionPath) -> WalkCallbackResult

// returns if the the walk was aborted
func walkDownAddress(_ value: Value, path: SmallProjectionPath,
                     visitUse: UseCallback, leafUses: inout Stack<(Operand, SmallProjectionPath)>) -> Bool {
  for use in value.uses {
    if use.isTypeDependent { continue }
    
    switch visitUse(use, path) {
    case .ignore:
      continue
    case .abortWalk:
      leafUses.push((use, path))
      return true
    case .continueWalk:
      break
    }
    
    let user = use.instruction
    
    switch user {
    case let sea as StructElementAddrInst:
      if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
        return walkDownAddress(sea, path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
    case let tea as TupleElementAddrInst:
      if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
        return walkDownAddress(tea, path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
    case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
      is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
      return walkDownAddress(user as! SingleValueInstruction, path: path, visitUse: visitUse, leafUses: &leafUses)
    case let mdi as MarkDependenceInst:
      if use.index == 0 {
        return walkDownAddress(mdi, path: path, visitUse: visitUse, leafUses: &leafUses)
      }
    default:
      leafUses.push((use, path))
    }
  }
  return false
}


/// NOTE: keep it symmetric to `walkDownAddress` as above
func walkUpAddress(_ value: Value, path: SmallProjectionPath,
                   visitDef: DefCallback, rootDefs: inout Stack<(Value, SmallProjectionPath)>) -> Bool {
  var val = value
  var p = path
  
  while true {
    switch visitDef(val, p) {
    case .ignore: return false
    case .abortWalk:
      rootDefs.push((val, p))
      return true
    case .continueWalk: break
    }
    
    switch val {
    case let sea as StructElementAddrInst:
      p = p.push(.structField, index: sea.fieldIndex)
      val = sea.operand
    case let tea as TupleElementAddrInst:
      p = p.push(.tupleField, index: tea.fieldIndex)
      val = tea.operand
    case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
      is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
      val = (val as! Instruction).operands[0].value
    case let mdi as MarkDependenceInst:
      // The first operand is the result
      val = mdi.operands[0].value
    default:
      rootDefs.push((val, path))
      return false
    }
  }
}

/// Given a `value` reaching a value of interest `v` and a `path` denoting the access path from `value` to `v`
/// find all uses of `v` and their `Path`. If the leaf use `v` has `Path("")` then that is a "immediate" use of `v`.
/// If the leaf `Path` is "s0.c1..." then the use is "transitive".
/// - When "constructor" instructions like `TupleInst`/`StructInst` are encountered
///   push the inverse of the construction (the selection) onto the path
/// - When projection instructions that match the path are encountered pop the selection
///   from the path since the value produced by the use is now "one level" down
func walkDownValue(_ value: Value, path: SmallProjectionPath,
                   visitUse: UseCallback, leafUses: inout Stack<(Operand, SmallProjectionPath)>) -> Bool {
  for use in value.uses {
    if use.isTypeDependent { continue }
    
    switch visitUse(use, path) {
    case .ignore:
      continue
    case .abortWalk:
      leafUses.push((use, path))
      return true
    case .continueWalk:
      break
    }
    
    let user = use.instruction
    
    switch user {
    case let str as StructInst:
      return walkDownValue(str, path: path.push(.structField, index: use.index),
                           visitUse: visitUse, leafUses: &leafUses)
    case let se as StructExtractInst:
      if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
        return walkDownValue(se, path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
    case let ds as DestructureStructInst:
      if let (index, newPath) = path.pop(kind: .structField) {
        return walkDownValue(ds.results[index], path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
      if path.topMatchesAnyValueField {
        for result in ds.results {
          if walkDownValue(result, path: path, visitUse: visitUse, leafUses: &leafUses) {
            return true
          }
        }
      } else {
        // NOTE: Conservative abort. Should be unreachable
        return true
      }
    case let dt as DestructureTupleInst:
      // Follow specific field
      if let (index, newPath) = path.pop(kind: .tupleField) {
        return walkDownValue(dt.results[index], path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
      // Follow all fields
      if path.topMatchesAnyValueField {
        for result in dt.results {
          if walkDownValue(result, path: path, visitUse: visitUse, leafUses: &leafUses) {
            return true
          }
        }
      } else {
        // NOTE: Conservative abort. Should be unreachable
        return true
      }
    case let t as TupleInst:
      return walkDownValue(t, path: path.push(.tupleField, index: use.index), visitUse: visitUse, leafUses: &leafUses)
    case let te as TupleExtractInst:
      if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
        return walkDownValue(te, path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
    case let e as EnumInst:
      return walkDownValue(e, path: path.push(.enumCase, index: e.caseIndex),
                           visitUse: visitUse, leafUses: &leafUses)
    case is UncheckedEnumDataInst, is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
      let svi = user as! SingleValueInstruction
      let caseIdx = (user as! EnumInstruction).caseIndex
      if let newPath = path.popIfMatches(.enumCase, index: caseIdx) {
        return walkDownValue(svi, path: newPath, visitUse: visitUse, leafUses: &leafUses)
      }
    case is InitExistentialRefInst, is OpenExistentialRefInst,
      is BeginBorrowInst, is CopyValueInst,
      is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
      is RefToBridgeObjectInst, is BridgeObjectToRefInst:
      return walkDownValue(user as! SingleValueInstruction, path: path, visitUse: visitUse, leafUses: &leafUses)
    case let bcm as BeginCOWMutationInst:
      return walkDownValue(bcm.bufferResult, path: path, visitUse: visitUse, leafUses: &leafUses)
    default:
      leafUses.push((use, path))
    }
  }
  return false
}

// NOTE: keep it symmetric to `walkDownValue`
func walkUpValue(_ value: Value, path: SmallProjectionPath,
                 visitDef: DefCallback, rootDefs: inout Stack<(Value, SmallProjectionPath)>) -> Bool {
  var val = value
  var p = path
  while true {
    switch visitDef(val, p) {
    case .ignore: return false
    case .abortWalk:
      rootDefs.push((val, p))
      return true
    case .continueWalk: break
    }
    
    switch val {
    case let str as StructInst:
      if let (structField, poppedPath) = p.pop(kind: .structField) {
        val = str.operands[structField].value
        p = poppedPath
      } else if p.topMatchesAnyValueField {
        for op in str.operands {
          if walkUpValue(op.value, path: path, visitDef: visitDef, rootDefs: &rootDefs) {
            return true
          }
        }
        return false
      } else {
        // NOTE: Conservative abort. Should be unreachable
        return true
      }
    case let se as StructExtractInst:
      val = se.operand
      p = p.push(.structField, index: se.fieldIndex)
    case let mvr as MultipleValueInstructionResult where mvr.instruction is DestructureStructInst:
      val = (mvr.instruction as! DestructureStructInst).operand
      p = p.push(.structField, index: mvr.index)
    case let mvr as MultipleValueInstructionResult where mvr.instruction is DestructureTupleInst:
      val = (mvr.instruction as! DestructureTupleInst).operand
      p = p.push(.tupleField, index: mvr.index)
    case let t as TupleInst:
      if let (tupleField, poppedPath) = p.pop(kind: .tupleField) {
        val = t.operands[tupleField].value
        p = poppedPath
      } else if p.topMatchesAnyValueField {
        for op in t.operands {
          if walkUpValue(op.value, path: path, visitDef: visitDef, rootDefs: &rootDefs) {
            return true
          }
        }
        return false
      } else {
        // NOTE: Conservative abort. Should be unreachable
        return true
      }
    case let te as TupleExtractInst:
      val = te.operand
      p = p.push(.tupleField, index: te.fieldIndex)
    case let e as EnumInst:
      guard let newPath = p.popIfMatches(.enumCase, index: e.caseIndex) else {
        return false
      }
      guard let op = e.operand else { return false }
      val = op
      p = newPath
    case is UncheckedEnumDataInst, is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
      val = (val as! UnaryInstruction).operand
      p = p.push(.enumCase, index: (val as! EnumInstruction).caseIndex)
    case is InitExistentialRefInst, is OpenExistentialRefInst,
      is BeginBorrowInst, is CopyValueInst,
      is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
      is RefToBridgeObjectInst, is BridgeObjectToRefInst:
      val = (val as! Instruction).operands[0].value
    case let mvr as MultipleValueInstructionResult where mvr.instruction is BeginCOWMutationInst:
      val = ((mvr.instruction as! BeginCOWMutationInst).operand)
    default:
      rootDefs.push((val, p))
      return false
    }
  }
}
