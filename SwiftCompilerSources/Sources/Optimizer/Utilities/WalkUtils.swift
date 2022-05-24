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

func TODO(_ message: String = "Unhandled TODO", fun: String = #function,
          file: String = #file, line: Int = #line) -> Never {
  fatalError("\(file):\(line) \(fun) \(message)")
}

public enum WalkResult {
  /// skip traversal
  case ignore
  /// stop the walk, add the current use/def and path to the result
  case abortWalk
  /// continue the walk
  case continueWalk
}

protocol MemoizedUp {
  mutating func shouldRecomputeUp(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
}

protocol MemoizedDown {
  mutating func shouldRecomputeDown(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
}

protocol ValueDefUseWalker : MemoizedDown {
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkResult
}

extension ValueDefUseWalker {
  private mutating
  func visitAndWalkDown(_ operand: Operand, path: SmallProjectionPath, values: Instruction.Results,
                        newPath: SmallProjectionPath) -> Bool {
    let maybeContinue = visitUse(ofValue: operand, path: path, isLeaf: false)
    switch maybeContinue {
    case .continueWalk:
      for result in values {
        if walkDown(value: result, path: newPath) {
          return true
        }
      }
      return false
    default:
      return maybeContinue == .abortWalk
    }
  }
  
  /// Note: keep it symmetric to `ValueUseDefWalker.walkUp`
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      var maybeLinearNext: (value: Value, path: SmallProjectionPath)? = nil

      // .none              : current not visited
      // .some(let aborted) : current and all recursive paths visited and `aborted = visitResult is .abortWalk`
      var visitAborted: Bool?
      
      let user = operand.instruction
      switch user {
      case let str as StructInst:
        maybeLinearNext = (str, path.push(.structField, index: operand.index))
      case let t as TupleInst:
        maybeLinearNext = (t, path.push(.tupleField, index: operand.index))
      case let br as BranchInst:
        let val = br.getArgument(for: operand)
        if let path = shouldRecomputeDown(value: val, path: path) {
          maybeLinearNext = (val, path)
        }
        maybeLinearNext = (br.getArgument(for: operand), path)
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          maybeLinearNext = (se, newPath)
        }
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          maybeLinearNext = (ds.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          // TODO: branching traversal?
          visitAborted = visitAndWalkDown(operand, path: path, values: ds.results, newPath: path)
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          maybeLinearNext = (dt.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          // TODO: branching traversal?
          visitAborted = visitAndWalkDown(operand, path: path, values: dt.results, newPath: path)
        }
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
      // "Forwarding" instructions
      case is UpcastInst, is UncheckedRefCastInst,
           is InitExistentialRefInst, is OpenExistentialRefInst,
           is InitExistentialAddrInst, is OpenExistentialAddrInst,
           is BeginAccessInst, is BeginBorrowInst,
           is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst,
           is IndexAddrInst, is CopyValueInst, is MarkDependenceInst,
           is PointerToAddressInst, is AddressToPointerInst:
        maybeLinearNext = (user as! SingleValueInstruction, path)
      case let bcm as BeginCOWMutationInst:
        maybeLinearNext = (bcm.bufferResult, path)
      default:
        break
      }
      
      if let aborted = visitAborted {
        // We have already visited and walked down in `DestructureStructInst` with
        // `.anyValueField` or similar.
        // Check if it is an abort, in which case return true (stopping the walk) but
        // no need to visit the current use which was handled by the `visitAndWalkDown` call above
        if aborted {
          return true
        }
      } else {
        // We still have to visit the current use
        let nextStep = visitUse(ofValue: operand, path: path, isLeaf: maybeLinearNext == nil)
        if nextStep == .abortWalk {
          return true
        } else if let (nextValue, nextPath) = maybeLinearNext,  // there is a next
            nextStep == .continueWalk &&                        // and client wants to continue
            walkDown(value: nextValue, path: nextPath) {        // visit, and if it is an abort return
          return true
        } else {
          // `nextStep == .ignore` Nothing to do.
          // Client might have returned `.continueWalk` but there is no next use
        }
      }
    }
    return false
  }
}

protocol ValueUseDefWalker : MemoizedUp {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkResult
}

extension ValueUseDefWalker {
  private mutating
  func visitAndWalkUp(value def: Value, path: SmallProjectionPath, operands: OperandArray,
                      newPath: SmallProjectionPath) -> Bool {
    let nextStep = visitDef(ofValue: def, path: path, isRoot: false)
    switch nextStep {
    case .abortWalk, .ignore:
      return nextStep == .abortWalk
    case .continueWalk:
      for op in operands {
        if let path = shouldRecomputeUp(value: op.value, path: newPath),
           walkUp(value: op.value, path: path) {
          return true
        }
      }
      return false
    }
  }
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `ValueDefUseWalker.walkDown`
  mutating
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
          return visitAndWalkUp(value: str, path: p, operands: str.operands, newPath: p)
        }
        // If reached, `next == nil` at the end of the switch which
        // meeans we reached a root and the walk will stop.
      case let t as TupleInst:
        if let (tupleField, poppedPath) = p.pop(kind: .tupleField) {
          maybeNext = (t.operands[tupleField].value, poppedPath)
        } else if p.topMatchesAnyValueField {
          return visitAndWalkUp(value: t, path: p, operands: t.operands, newPath: p)
        }
        // If reached, `next == nil` at the end of the switch which
        // meeans we reached a root and the walk will stop.
      case let arg as BlockArgument:
        if arg.isPhiArgument {
          let nextStep = visitDef(ofValue: arg, path: p, isRoot: false)
          switch nextStep {
          case .abortWalk, .ignore:
            return nextStep == .abortWalk
          case .continueWalk:
            for incoming in arg.incomingPhiValues {
              if let path = shouldRecomputeUp(value: incoming, path: p),
                 walkUp(value: incoming, path: path) {
                return true
              }
            }
            return false
          }
        } else {
          TODO("enum/try_apply block argument")
        }
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
      // "Forwarding" instructions
      case is UpcastInst, is UncheckedRefCastInst,
           is InitExistentialRefInst, is OpenExistentialRefInst,
           is InitExistentialAddrInst, is OpenExistentialAddrInst,
           is BeginAccessInst, is BeginBorrowInst,
           is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst,
           is IndexAddrInst, is CopyValueInst, is MarkDependenceInst,
           is PointerToAddressInst, is AddressToPointerInst:
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

protocol AddressDefUseWalker : MemoizedDown {
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkResult
}

extension AddressDefUseWalker {
  /// - Returns: if the walk is aborted
  // Note: keep it symmetric to `AddressUseDefWalker.walkUp`
  mutating
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
      case let br as BranchInst:
        let val = br.getArgument(for: use)
        if let path = shouldRecomputeDown(value: val, path: path) {
          maybeNext = (val, path)
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

protocol AddressUseDefWalker : MemoizedUp {
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkResult
}

extension AddressUseDefWalker {
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `AddressDefUseWalker.walkDown`
  mutating
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
      case let arg as BlockArgument:
        if arg.isPhiArgument {
          let nextStep = visitDef(ofAddress: arg, path: p, isRoot: false)
          switch nextStep {
          case .abortWalk, .ignore:
            return nextStep == .abortWalk
          case .continueWalk:
            for incoming in arg.incomingPhiValues {
              if let path = shouldRecomputeUp(value: incoming, path: p),
                 walkUp(address: incoming, path: path) {
                return true
              }
            }
            return false
          }
        } else {
          TODO("enum/try_apply block argument")
        }
      default:
        break
      }
      
      // 2. Visit the _current_ definition
      let nextStep = visitDef(ofAddress: val, path: p, isRoot: maybeNext == nil)
      
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
