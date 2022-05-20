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
import Darwin

public enum WalkCallbackResult {
  /// skip traversal
  case ignore
  /// stop the walk, add the current use/def and path to the result
  case abortWalk
  /// continue the walk
  case continueWalk
}

protocol ValueDefUseWalker {
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkCallbackResult
}

extension ValueDefUseWalker {
  private
  func visitAndWalkDown(_ operand: Operand, path: SmallProjectionPath, values: Instruction.Results,
                                  newPath: SmallProjectionPath) -> Bool {
    let maybeContinue = visitUse(ofValue: operand, path: path, isLeaf: false)
    switch maybeContinue {
    case .continueWalk:
      for result in values {
        if walkDown(value: result, path: path) {
          return true
        }
      }
      return false
    default:
      return maybeContinue == .abortWalk
    }
  }
  
  /// Note: keep it symmetric to `ValueUseDefWalker.walkUp`
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    var abortWalk = false
    
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      var maybeLinearNext: (value: Value, path: SmallProjectionPath)? = nil
      var visited = false
      
      let user = operand.instruction
      switch user {
      case let str as StructInst:
        maybeLinearNext = (str, path.push(.structField, index: operand.index))
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          maybeLinearNext = (se, newPath)
        }
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          maybeLinearNext = (ds.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          abortWalk = visitAndWalkDown(operand, path: path, values: ds.results, newPath: path)
          visited = true
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          maybeLinearNext = (dt.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          abortWalk = visitAndWalkDown(operand, path: path, values: dt.results, newPath: path)
          visited = true
        }
      case let t as TupleInst:
        maybeLinearNext = (t, path.push(.tupleField, index: operand.index))
      case let te as TupleExtractInst:
        if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
          maybeLinearNext = (te, newPath)
        }
      case let e as EnumInst:
        maybeLinearNext = (e, path.push(.enumCase, index: e.caseIndex))
      case is UncheckedEnumDataInst, is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let svi = user as! SingleValueInstruction
        let caseIdx = (user as! EnumInstruction).caseIndex
        if let newPath = path.popIfMatches(.enumCase, index: caseIdx) {
          maybeLinearNext = (svi, newPath)
        }
      case is InitExistentialRefInst, is OpenExistentialRefInst,
        is BeginBorrowInst, is CopyValueInst,
        is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
        is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        maybeLinearNext = (user as! SingleValueInstruction, path)
      case let bcm as BeginCOWMutationInst:
        maybeLinearNext = (bcm.bufferResult, path)
      default:
        break
      }
      
      // Branching cases like `DestructureStructInst` with `.anyValueField`
      // visit and continue the walk on their own and set the `visited` value
      if !visited {
        let isLeaf = maybeLinearNext == nil
        let nextStep = visitUse(ofValue: operand, path: path, isLeaf: isLeaf)
        if let (nextValue, nextPath) = maybeLinearNext, nextStep == .continueWalk {
          abortWalk = walkDown(value: nextValue, path: nextPath)
        } else if nextStep == .abortWalk {
          return true
        } else {
          // 3b. nextStep == .ignore
          //     Nothing to do. Client might have returned `.continueWalk` but there is no follow
        }
      }
      // A visit and then branch in `DestructureStructInst` with `.anyValueField`
      // might have requested an abort. Shortcircuit
      if abortWalk {
        return true
      }
    }
    return false
  }
}

protocol ValueUseDefWalker {
  func visitDef(ofValue value: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkCallbackResult
}

extension ValueUseDefWalker {
  private
  func visitAndWalkUp(value def: Value, path: SmallProjectionPath, operands: OperandArray,
                                   newPath: SmallProjectionPath) -> Bool {
    let nextStep = visitDef(ofValue: def, path: path, isRoot: false)
    switch nextStep {
    case .abortWalk, .ignore:
      return nextStep == .abortWalk
    case .continueWalk:
      for op in operands {
        if walkUp(value: op.value, path: path) {
          return true
        }
      }
      return false
    }
  }
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `ValueDefUseWalker.walkDown`
  func walkUp(value def: Value, path: SmallProjectionPath) -> Bool {
    var current: (value: Value, path: SmallProjectionPath) = (def, path)
    
    while true {
      
      // 1. First compute if we will continue the walk and what will be the
      //    `next` `value` and `path` so we can pass `isRoot` to the `visitDef` of the _current_ definition.
      //    In case of the walk branching, that will be a recursive call so
      //    we return right away.
      var maybeNext: (value: Value, path: SmallProjectionPath)? = nil
      
      let (val, p) = current
      switch val {
      case let str as StructInst:
        if let (structField, poppedPath) = p.pop(kind: .structField) {
          maybeNext = (str.operands[structField].value, poppedPath)
        } else if p.topMatchesAnyValueField {
          // Branch, TODO: cache
          return visitAndWalkUp(value: str, path: p, operands: str.operands, newPath: p)
        }
        // If reached, `next == nil` at the end of the switch which
        // meeans we reached a root and the walk will stop.
      case let se as StructExtractInst:
        maybeNext = (se.operand, p.push(.structField, index: se.fieldIndex))
      case let mvr as MultipleValueInstructionResult where mvr.instruction is DestructureStructInst:
        maybeNext = (
          (mvr.instruction as! DestructureStructInst).operand,
          p.push(.structField, index: mvr.index)
        )
      case let mvr as MultipleValueInstructionResult where mvr.instruction is DestructureTupleInst:
        maybeNext = (
          (mvr.instruction as! DestructureTupleInst).operand,
          p.push(.tupleField, index: mvr.index)
        )
      case let t as TupleInst:
        if let (tupleField, poppedPath) = p.pop(kind: .tupleField) {
          maybeNext = (t.operands[tupleField].value, poppedPath)
        } else if p.topMatchesAnyValueField {
          // Branch, TODO: cache
          return visitAndWalkUp(value: t, path: p, operands: t.operands, newPath: p)
        }
        // If reached, `next == nil` at the end of the switch which
        // meeans we reached a root and the walk will stop.
      case let te as TupleExtractInst:
        maybeNext = (te.operand, p.push(.tupleField, index: te.fieldIndex))
      case let e as EnumInst:
        if let popped = p.popIfMatches(.enumCase, index: e.caseIndex),
           let op = e.operand {
          maybeNext = (op, popped)
        }
        // If reached, `next == nil` at the end of the switch which
        // meeans we reached a root and the walk will stop.
      case is UncheckedEnumDataInst, is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        maybeNext = (
          (val as! UnaryInstruction).operand,
          p.push(.enumCase, index: (val as! EnumInstruction).caseIndex)
        )
      case is InitExistentialRefInst, is OpenExistentialRefInst,
        is BeginBorrowInst, is CopyValueInst,
        is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
        is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        maybeNext = ((val as! Instruction).operands[0].value, p)
      case let mvr as MultipleValueInstructionResult where mvr.instruction is BeginCOWMutationInst:
        maybeNext = ((mvr.instruction as! BeginCOWMutationInst).operand, p)
      default:
        break
      }
      
      let isRoot = maybeNext == nil
      // 2. Visit the _current_ definition
      let nextStep = visitDef(ofValue: val, path: p, isRoot: isRoot)
      
      if let next = maybeNext, nextStep == .continueWalk {
        // 3a. Set current to next and continue the walk
        current = (next.value, next.path)
      } else if nextStep == .abortWalk {
        // Client requests to not visit the other uses
        return true
      } else {
        // 3b. nextStep == .ignore
        //     Nothing to do. Client might have returned `.continueWalk` but there is no follow
        return false
      }
    }
  }
}

protocol AddressDefUseWalker {
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkCallbackResult
}

extension AddressDefUseWalker {
  /// - Returns: if the walk is aborted
  // Note: keep it symmetric to `AddressUseDefWalker.walkUp`
  func walkDown(address def: Value, path: SmallProjectionPath) -> Bool {
    for use in def.uses {
      if use.isTypeDependent { continue }
      
      var maybeNext: (def: Value, path: SmallProjectionPath)? = nil
      
      let user = use.instruction
      switch user {
      case let sea as StructElementAddrInst:
        if let nextPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
          maybeNext = (sea, nextPath)
        }
      case let tea as TupleElementAddrInst:
        if let nextPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
          maybeNext = (tea, nextPath)
        }
      // Forwarding instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
        is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        // Forwarding instructions
        maybeNext = (user as! SingleValueInstruction, path)
      case let mdi as MarkDependenceInst:
        // Forwarding instruction if use is the first operand
        if use.index == 0 {
          maybeNext = (mdi, path)
        }
      default:
        break
      }
      
      let isLeaf = maybeNext == nil
      
      let nextStep = visitUse(ofAddress: use, path: path, isLeaf: isLeaf)
      
      if let next = maybeNext, nextStep == .continueWalk {
        if walkDown(address: next.def, path: next.path) {
          // Client requests to not visit the other uses
          return true
        }
      } else if nextStep == .abortWalk {
        // Client requests to not visit the other uses
        return true
      } else {
        // nextStep == .ignore
        // Nothing to do. Client might have returned .continueWalk but there is no follow
      }
    }
    return false
  }
}

protocol AddressUseDefWalker {
  func visitDef(ofAddress: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkCallbackResult
}

extension AddressUseDefWalker {
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `AddressDefUseWalker.walkDown`
  func walkUp(address def: Value, path: SmallProjectionPath) -> Bool {
    var current = (def, path)
    
    while true {
      
      // 1. First compute if we will continue the walk and what will be the
      //    `next` `operand` and `path` so we can pass `isRoot` to the `visitAddressDef` of the _current_ definition.
      var maybeNext: (operand: Value, path: SmallProjectionPath)? = nil
      
      let (val, p) = current
      switch val {
      case let sea as StructElementAddrInst:
        maybeNext = (sea.operand, p.push(.structField, index: sea.fieldIndex))
      case let tea as TupleElementAddrInst:
        maybeNext = (tea.operand, p.push(.tupleField, index: tea.fieldIndex))
      // Forwarding instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
        is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        maybeNext = ((val as! Instruction).operands[0].value, p)
      case let mdi as MarkDependenceInst:
        maybeNext = (mdi.operands[0].value, p)
      default:
        break
      }
      
      let isRoot = maybeNext == nil
      // 2. Visit the _current_ definition
      let nextStep = visitDef(ofAddress: val, path: p, isRoot: isRoot)
      
      if let next = maybeNext, nextStep == .continueWalk {
        // 3a. Set current to next and continue the walk
        current = (next.operand, next.path)
      } else if nextStep == .abortWalk {
        // Client requests to not visit the other uses
        return true
      } else {
        // nextStep == .ignore
        // Nothing to do. Client might have returned `.continueWalk` but there is no follow
        return false
      }
    }
  }
}
