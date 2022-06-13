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


protocol MemoizedDefUse {
  typealias Path = SmallProjectionPath
  associatedtype State
  
  mutating func shouldRecomputeDown(def: Value, path: Path, state: State) -> (Path, State)?
}

protocol MemoizedUseDef {
  typealias Path = SmallProjectionPath
  associatedtype State
  
  mutating func shouldRecomputeUp(def: Value, path: Path, state: State) -> (Path, State)?
}

protocol ValueDefUseWalker : MemoizedDefUse {
  mutating func walkDown(value: Operand, path: Path, state: State) -> Bool
  
  mutating func leafUse(value: Operand, path: Path, state: State) -> Bool
  
  mutating func unmatchedPath(value: Operand, path: Path, state: State) -> Bool
}


extension ValueDefUseWalker {
  mutating func walkDown(value operand: Operand, path: Path, state: State) -> Bool {
    return walkDownDefault(value: operand, path: path, state: state)
  }
  
  mutating func unmatchedPath(value: Operand, path: Path, state: State) -> Bool {
    return false
  }
  
  mutating func walkDownDefault(value operand: Operand, path: Path, state: State) -> Bool {
    let instruction = operand.instruction
    switch instruction {
    case let str as StructInst:
      return walkDownUses(value: str,
                      path: path.push(.structField, index: operand.index),
                      state: state)
    case let t as TupleInst:
      return walkDownUses(value: t,
                      path: path.push(.tupleField, index: operand.index),
                      state: state)
    case let e as EnumInst:
      return walkDownUses(value: e,
                          path: path.push(.enumCase, index: e.caseIndex),
                          state: state)
    case let se as StructExtractInst:
      if let path = path.popIfMatches(.structField, index: se.fieldIndex) {
        return walkDownUses(value: se, path: path, state: state)
      } else {
        return unmatchedPath(value: operand, path: path, state: state)
      }
    case let te as TupleExtractInst:
      if let path = path.popIfMatches(.tupleField, index: te.fieldIndex) {
        return walkDownUses(value: te, path: path, state: state)
      } else {
        return unmatchedPath(value: operand, path: path, state: state)
      }
    case let ued as UncheckedEnumDataInst:
      if let path = path.popIfMatches(.enumCase, index: ued.caseIndex) {
        return walkDownUses(value: ued, path: path, state: state)
      } else {
        return unmatchedPath(value: operand, path: path, state: state)
      }
    case let ds as DestructureStructInst:
      if let (index, path) = path.pop(kind: .structField) {
        return walkDownUses(value: ds.results[index], path: path, state: state)
      } else if path.topMatchesAnyValueField {
        return walkDownUses(resultsOf: ds, path: path, state: state)
      } else {
        return unmatchedPath(value: operand, path: path, state: state)
      }
    case let dt as DestructureTupleInst:
      if let (index, path) = path.pop(kind: .tupleField) {
        return walkDownUses(value: dt.results[index], path: path, state: state)
      } else if path.topMatchesAnyValueField {
        return walkDownUses(resultsOf: dt, path: path, state: state)
      } else {
        return unmatchedPath(value: operand, path: path, state: state)
      }
    case is InitExistentialRefInst, is OpenExistentialRefInst,
      is BeginBorrowInst, is CopyValueInst,
      is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
      is RefToBridgeObjectInst, is BridgeObjectToRefInst:
      return walkDownUses(value: (instruction as! SingleValueInstruction), path: path, state: state)
    case is MarkDependenceInst:
      assert(operand.index == 1)
      return unmatchedPath(value: operand, path: path, state: state)
    case let br as BranchInst:
      let val = br.getArgument(for: operand)
      if let (path, state) = shouldRecomputeDown(def: val, path: path, state: state) {
        return walkDownUses(value: val, path: path, state: state)
      } else {
        return false
      }
    case let cbr as CondBranchInst:
      let val = cbr.getArgument(for: operand)
      if let (path, state) = shouldRecomputeDown(def: val, path: path, state: state) {
        return walkDownUses(value: val, path: path, state: state)
      } else {
        return false
      }
    case let bcm as BeginCOWMutationInst:
      return walkDownUses(value: bcm.bufferResult, path: path, state: state)
    default:
      return leafUse(value: operand, path: path, state: state)
    }
  }
  
  mutating func walkDownUses(value: Value, path: Path, state: State) -> Bool {
    for operand in value.uses where !operand.isTypeDependent {
      if walkDown(value: operand, path: path, state: state) {
        return true
      }
    }
    return false
  }
  
  mutating func walkDownUses(resultsOf value: MultipleValueInstruction, path: Path, state: State) -> Bool {
    for result in value.results {
      if let (path, state) = shouldRecomputeDown(def: result, path: path, state: state) {
        if walkDownUses(value: result, path: path, state: state) {
          return true
        }
      }
    }
    return false
  }
}

protocol AddressDefUseWalker : MemoizedDefUse {
  mutating func walkDown(address: Operand, path: Path, state: State) -> Bool
  
  mutating func leafUse(address: Operand, path: Path, state: State) -> Bool
  
  mutating func unmatchedPath(address: Operand, path: Path, state: State) -> Bool
}


extension AddressDefUseWalker {
  mutating func walkDown(address operand: Operand, path: Path, state: State) -> Bool {
    return walkDownDefault(address: operand, path: path, state: state)
  }
  
  mutating func unmatchedPath(address: Operand, path: Path, state: State) -> Bool {
    return false
  }
  
  mutating func walkDownDefault(address operand: Operand, path: Path, state: State) -> Bool {
    let instruction = operand.instruction
    switch instruction {
    case let sea as StructElementAddrInst:
      if let path = path.popIfMatches(.structField, index: sea.fieldIndex) {
        return walkDownUses(address: sea, path: path, state: state)
      } else {
        return unmatchedPath(address: operand, path: path, state: state)
      }
    case let tea as TupleElementAddrInst:
      if let path = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
        return walkDownUses(address: tea, path: path, state: state)
      } else {
        return unmatchedPath(address: operand, path: path, state: state)
      }
    case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
      let ei = instruction as! SingleValueInstruction
      if let path = path.popIfMatches(.enumCase, index: (instruction as! EnumInstruction).caseIndex) {
        return walkDownUses(address: ei, path: path, state: state)
      } else {
        return unmatchedPath(address: operand, path: path, state: state)
      }
    case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
      is IndexAddrInst:
      return walkDownUses(address: instruction as! SingleValueInstruction, path: path, state: state)
    case let mdi as MarkDependenceInst:
      assert(operand.index == 0)
      return walkDownUses(address: mdi, path: path, state: state)
    default:
      return leafUse(address: operand, path: path, state: state)
    }
  }
  
  mutating func walkDownUses(address: Value, path: Path, state: State) -> Bool {
    for operand in address.uses where !operand.isTypeDependent {
      if walkDown(address: operand, path: path, state: state) {
        return true
      }
    }
    return false
  }
}

protocol ValueUseDefWalker : MemoizedUseDef {
  associatedtype State
  
  mutating func walkUp(value: Value, path: Path, state: State) -> Bool
  
  mutating func rootDef(value: Value, path: Path, state: State) -> Bool
  
  mutating func unmatchedPath(value: Value, path: Path, state: State) -> Bool
}

extension ValueUseDefWalker {
  mutating func walkUp(value: Value, path: Path, state: State) -> Bool {
    return walkUpDefault(value: value, path: path, state: state)
  }
  
  mutating func unmatchedPath(value: Value, path: Path, state: State) -> Bool {
    return false
  }
  
  mutating func walkUpDefault(value def: Value, path: Path, state: State) -> Bool {
    switch def {
    case let str as StructInst:
      if let (index, path) = path.pop(kind: .structField) {
        return walkUp(value: str.operands[index].value, path: path, state: state)
      } else if path.topMatchesAnyValueField {
        return walkUp(operandsOf: str, path: path, state: state)
      } else {
        return unmatchedPath(value: str, path: path, state: state)
      }
    case let t as TupleInst:
      if let (index, path) = path.pop(kind: .tupleField) {
        return walkUp(value: t.operands[index].value, path: path, state: state)
      } else if path.topMatchesAnyValueField {
        return walkUp(operandsOf: t, path: path, state: state)
      } else {
        return unmatchedPath(value: t, path: path, state: state)
      }
    case let e as EnumInst:
      if let path = path.popIfMatches(.enumCase, index: e.caseIndex),
         let operand = e.operand {
        return walkUp(value: operand, path: path, state: state)
      } else {
        return unmatchedPath(value: e, path: path, state: state)
      }
    case let se as StructExtractInst:
      return walkUp(value: se.operand, path: path.push(.structField, index: se.fieldIndex), state: state)
    case let te as TupleExtractInst:
      return walkUp(value: te.operand, path: path.push(.tupleField, index: te.fieldIndex), state: state)
    case let ued as UncheckedEnumDataInst:
      return walkUp(value: ued.operand, path: path.push(.enumCase, index: ued.caseIndex), state: state)
    case let mvr as MultipleValueInstructionResult:
      let instruction = mvr.instruction
      if let ds = instruction as? DestructureStructInst {
        return walkUp(value: ds.operand, path: path.push(.structField, index: mvr.index), state: state)
      } else if let dt = instruction as? DestructureTupleInst {
        return walkUp(value: dt.operand, path: path.push(.tupleField, index: mvr.index), state: state)
      } else if let bcm = instruction as? BeginCOWMutationInst {
        return walkUp(value: bcm.operand, path: path, state: state)
      } else {
        return rootDef(value: mvr, path: path, state: state)
      }
    case is InitExistentialRefInst, is OpenExistentialRefInst,
      is BeginBorrowInst, is CopyValueInst,
      is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
      is RefToBridgeObjectInst, is BridgeObjectToRefInst:
      return walkUp(value: (def as! Instruction).operands[0].value, path: path, state: state)
    case let arg as BlockArgument where arg.isPhiArgument:
      for incoming in arg.incomingPhiValues {
        if let (path, state) = shouldRecomputeUp(def: incoming, path: path, state: state) {
          if walkUp(value: incoming, path: path, state: state) {
            return true
          }
        }
      }
      return false
    default:
      return rootDef(value: def, path: path, state: state)
    }
  }
  
  mutating func walkUp(operandsOf def: SingleValueInstruction, path: Path, state: State) -> Bool {
    for operand in def.operands {
      if let (path, state) = shouldRecomputeUp(def: operand.value, path: path, state: state) {
        if walkUp(value: operand.value, path: path, state: state) {
          return true
        }
      }
    }
    return false
  }
  
}

protocol AddressUseDefWalker : MemoizedUseDef {
  mutating func walkUp(address: Value, path: Path, state: State) -> Bool
  
  mutating func rootDef(address: Value, path: Path, state: State) -> Bool
  
  mutating func unmatchedPath(address: Value, path: Path, state: State) -> Bool
}

extension AddressUseDefWalker {
  
  mutating func walkUp(address: Value, path: Path, state: State) -> Bool {
    return walkUpDefault(address: address, path: path, state: state)
  }
  
  mutating func unmatchedPath(address: Value, path: Path, state: State) -> Bool {
    return false
  }
  
  mutating func walkUpDefault(address def: Value, path: Path, state: State) -> Bool {
    switch def {
    case let sea as StructElementAddrInst:
      return walkUp(address: sea.operand, path: path.push(.structField, index: sea.fieldIndex), state: state)
    case let tea as TupleElementAddrInst:
      return walkUp(address: tea.operand, path: path.push(.tupleField, index: tea.fieldIndex), state: state)
    case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
      return walkUp(address: (def as! UnaryInstruction).operand,
                    path: path.push(.enumCase, index: (def as! EnumInstruction).caseIndex), state: state)
    case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst, is IndexAddrInst:
      return walkUp(address: (def as! Instruction).operands[0].value, path: path, state: state)
    case let mdi as MarkDependenceInst:
      return walkUp(address: mdi.operands[0].value, path: path, state: state)
    default:
      return rootDef(address: def, path: path, state: state)
    }
  }
}
