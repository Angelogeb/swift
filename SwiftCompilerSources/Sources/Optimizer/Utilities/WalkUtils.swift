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

enum WalkResult {
  /// stop walking further for the current use/definition
  case stopWalk
  /// abort the walk for all uses/definitions
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
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkResult {
    return .continueWalk
  }
  
  /// Note: keep it symmetric to `ValueUseDefWalker.walkUp`
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      // .none              : current not visited
      // .some(let aborted) : current and all recursive paths visited and `aborted = visitResult is .abortWalk`
      var visitAborted: Bool?
      
      var maybeLinearNext = resultPath(value: operand, path: path)
      switch maybeLinearNext {
      case .unmatchedPath:
        let inst = operand.instruction
        if path.topMatchesAnyValueField &&
            (inst is DestructureStructInst || inst is DestructureTupleInst) {
          visitAborted = handleDestructureAnyValueField(operand, path: path,
                                          values: inst.results, newPath: path)
        } else {
          fatalError("Inconsistent state? Path (\(path) does not match instruction \(operand.instruction)")
        }
      case .unmatchedInstruction:
        switch operand.instruction {
        case let br as BranchInst:
          let val = br.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            maybeLinearNext = .some(val, path)
          }
        case let cbr as CondBranchInst:
          assert(operand.index != 0, "should not visit trivial non-address values")
          let val = cbr.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            maybeLinearNext = .some(val, path)
          }
        default:
          break
        }
      case .some(_, _):
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
        let nextStep = visitUse(ofValue: operand, path: path,
                                isLeaf: maybeLinearNext.isUnmatchedInstruction)
        switch nextStep {
        case .stopWalk:
          break
        case .abortWalk:
          return true
        case .continueWalk:
          if case let .some(nextValue, nextPath) = maybeLinearNext,
             walkDown(value: nextValue, path: nextPath) {
            return true
          }
        }
      }
    }
    return false
  }
  
  private mutating
  func handleDestructureAnyValueField(_ operand: Operand, path: SmallProjectionPath, values: Instruction.Results,
                        newPath: SmallProjectionPath) -> Bool {
    let maybeContinue = visitUse(ofValue: operand, path: path, isLeaf: false)
    switch maybeContinue {
    case .abortWalk:
      return true
    case .stopWalk:
      return false
    case .continueWalk:
      for result in values {
        // TODO: insert shouldRecomputeDown call?
        // EscapeInfo doesn't
        if walkDown(value: result, path: newPath) {
          return true
        }
      }
      return false
    }
  }
}

protocol ValueUseDefWalker : MemoizedUp {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                isRoot: Bool) -> WalkResult
}

extension ValueUseDefWalker {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                isRoot: Bool)  -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `ValueDefUseWalker.walkDown`
  mutating
  func walkUp(value def: Value, path: SmallProjectionPath) -> Bool {
    var current: (value: Value, path: SmallProjectionPath) = (def, path)
    
    while true {
      let (value, path) = current
      // 1. First compute if we will continue the walk and what will be the
      //    `next` `value` and `path` so we can pass `isRoot` to the `visitDef`
      //    of the _current_ definition.
      var maybeNext = operandDefinition(value: value, path: path)
      
      switch maybeNext {
      case .unmatchedPath:
        let (value, path) = current
        if path.topMatchesAnyValueField && (value is StructInst || value is TupleInst) {
          // In case of the walk branching, the recursive call will handle
          // the rest of the walk, so we return right away
          return visitAndWalkUp(value: value, path: path,
                                operands: (value as! Instruction).operands, newPath: path)
        } else {
          fatalError("Inconsistent state? Path (\(path) does not match instruction \(value)")
        }
      case .unmatchedInstruction:
        if let arg = value as? BlockArgument {
          if arg.isPhiArgument {
            let nextStep = visitDef(ofValue: arg, path: path, isRoot: false)
            switch nextStep {
            case .abortWalk:
              return true
            case .stopWalk:
              return false
            case .continueWalk:
              for incoming in arg.incomingPhiValues {
                if let path = shouldRecomputeUp(value: incoming, path: path),
                   walkUp(value: incoming, path: path) {
                  return true
                }
              }
              return false
            }
          } else {
            let block = arg.block
            switch block.singlePredecessor!.terminator {
            case let se as SwitchEnumInst:
              if let caseIdx = se.getUniqueCase(forSuccessor: block) {
                maybeNext = .some(se.enumOp, path.push(.enumCase, index: caseIdx))
              } else {
                // NOTE: ("EscapeInfo returns .abortWalk (isEscaping)")
                // here instead we leave maybeNext as .unmatchedInstruction
                // so the caller knows that this is a root according
                // to the traversal and therefore can abort
              }
            case is TryApplyInst:
              fatalError("Remember to handle TryApplyInst in clients")
            default:
              break
            }
          }
        }
      case .some(_, _):
        break
      }
      
      // 2. Visit the _current_ definition
      let nextStep = visitDef(ofValue: value, path: path,
                              isRoot: maybeNext.isUnmatchedInstruction)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if case let .some(val, p) = maybeNext {
          current = (val, p)
        }
      }
    }
  }

  private mutating
  func visitAndWalkUp(value def: Value, path: SmallProjectionPath, operands: OperandArray,
                      newPath: SmallProjectionPath) -> Bool {
    let nextStep = visitDef(ofValue: def, path: path, isRoot: false)
    switch nextStep {
    case .abortWalk:
      return true
    case .stopWalk:
      return false
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
}

protocol AddressDefUseWalker : MemoizedDown {
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                isLeaf: Bool) -> WalkResult
}

extension AddressDefUseWalker {
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                isLeaf: Bool) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: if the walk is aborted
  // Note: keep it symmetric to `AddressUseDefWalker.walkUp`
  mutating
  func walkDown(address def: Value, path: SmallProjectionPath) -> Bool {
    for use in def.uses {
      if use.isTypeDependent { continue }
      
      let maybeNext = resultPath(addr: use, path: path)
      
      switch maybeNext {
      case .unmatchedPath:
        fatalError("Inconsistent state? Path (\(path) does not match instruction \(use)")
      default:
        break
      }
      
      let nextStep = visitUse(ofAddress: use, path: path,
                              isLeaf: maybeNext.isUnmatchedInstruction)
      
      switch nextStep {
      case .stopWalk:
        break
      case .abortWalk:
        return true
      case .continueWalk:
        if case let .some(addr, p) = maybeNext,
          walkDown(address: addr, path: p) {
          return true
        }
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
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  /// Note: keep it symmetric to `AddressDefUseWalker.walkDown`
  mutating
  func walkUp(address def: Value, path: SmallProjectionPath) -> Bool {
    var current = (def, path)
    
    while true {
      let (addr, p) = current
      // 1. First compute if we will continue the walk and what will be the
      //    `next` `operand` and `path` so we can pass `isRoot` to the `visitAddressDef` of the _current_ definition.
      var maybeNext = operandDefinition(addr: addr, path: p)
      switch maybeNext {
      case .unmatchedInstruction:
        if let arg = addr as? BlockArgument {
          if arg.isPhiArgument {
            let nextStep = visitDef(ofAddress: arg, path: path, isRoot: false)
            switch nextStep {
            case .abortWalk:
              return true
            case .stopWalk:
              return false
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
            let block = arg.block
            switch block.singlePredecessor!.terminator {
            case let se as SwitchEnumInst:
              if let caseIdx = se.getUniqueCase(forSuccessor: block) {
                maybeNext = .some(se.enumOp, p.push(.enumCase, index: caseIdx))
              } else {
                // NOTE: ("EscapeInfo returns .abortWalk (isEscaping)")
                // here instead we leave maybeNext as .unmatchedInstruction
                // so the caller knows that this is a root according
                // to the traversal and therefore can abort
              }
            case is TryApplyInst:
              fatalError("Remember to handle TryApplyInst in clients")
            default:
              break
            }
          }
        }
      case .unmatchedPath:
        fatalError("Inconsistent state? Path (\(path) does not match instruction \(def)")
      case .some(_, _):
        break
      }
      
      // 2. Visit the _current_ definition
      let nextStep = visitDef(ofAddress: addr, path: p,
                              isRoot: maybeNext.isUnmatchedInstruction)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if case let .some(nextAddr, nextPath) = maybeNext {
          current = (nextAddr, nextPath)
        }
      }
    }
  }
}
