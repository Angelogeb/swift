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

protocol DefUseWalker {
  mutating
  func shouldRecomputeDown(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
  
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath,
                isLeaf: Bool) -> WalkResult
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                isLeaf: Bool) -> WalkResult
}

extension DefUseWalker {
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath, isLeaf: Bool) -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                isLeaf: Bool) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `UseDefWalker.walkUp(value:`
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      var visited = false
      var maybeNext: (Value, SmallProjectionPath)?
      
      let instruction = operand.instruction
      switch instruction {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        maybeNext = (str, path.push(.structField, index: operand.index))
      case let t as TupleInst:
        maybeNext = (t, path.push(.tupleField, index: operand.index))
      case let e as EnumInst:
        maybeNext = (e, path.push(.enumCase, index: e.caseIndex))
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          maybeNext = (se, newPath)
        }
      case let te as TupleExtractInst:
        if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
          maybeNext = (te, newPath)
        }
      case let ued as UncheckedEnumDataInst:
        if let newPath = path.popIfMatches(.enumCase, index: ued.caseIndex) {
          maybeNext = (ued, newPath)
        }
      // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          maybeNext = (ds.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          if handleDestructureAnyValueField(operand, path: path,
                                            values: instruction.results, newPath: path) {
            return true
          }
          visited = true
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          maybeNext = (dt.results[index], newPath)
        } else if path.topMatchesAnyValueField {
          if handleDestructureAnyValueField(operand, path: path,
                                            values: instruction.results, newPath: path) {
            return true
          }
          visited = true
        }
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        maybeNext = (instruction as! SingleValueInstruction, path)
      case let bcm as BeginCOWMutationInst:
        maybeNext = (bcm.bufferResult, path)
      // MARK: Non-Address Branching Instructions
      case let br as BranchInst:
        let val = br.getArgument(for: operand)
        if let path = shouldRecomputeDown(value: val, path: path) {
          maybeNext = (val, path)
        }
      case let cbr as CondBranchInst:
        assert(operand.index != 0, "should not visit trivial non-address values")
        let val = cbr.getArgument(for: operand)
        if let path = shouldRecomputeDown(value: val, path: path) {
          maybeNext = (val, path)
        }
      default:
        break
      }
      
      if !visited {
        // We still have to visit the current use
        let nextStep = visitUse(ofValue: operand, path: path, isLeaf: maybeNext == nil)
        switch nextStep {
        case .stopWalk:
          break
        case .abortWalk:
          return true
        case .continueWalk:
          if let (nextValue, nextPath) = maybeNext,
             walkDown(value: nextValue, path: nextPath) {
            return true
          }
        }
      }
    }
    return false
  }
  
  /// - Returns: if the walk is aborted
  // Note: keep it symmetric to `UseDefWalker.walkUp(address:`
  mutating
  func walkDown(address def: Value, path: SmallProjectionPath) -> Bool {
    for use in def.uses {
      if use.isTypeDependent { continue }
      
      var maybeNext: (Value, SmallProjectionPath)?
      
      let instruction = use.instruction
      switch instruction {
      // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
          maybeNext = (sea, newPath)
        }
      case let tea as TupleElementAddrInst:
        if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
          maybeNext = (tea, newPath)
        }
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = instruction as! EnumInst
        if let newPath = path.popIfMatches(.enumCase, index: ei.caseIndex) {
          maybeNext = (ei, newPath)
        }
      // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
           is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        maybeNext = (instruction as! SingleValueInstruction, path)
      case let mdi as MarkDependenceInst:
        if use.index == 0 {
          maybeNext = (mdi, path)
        }
      default:
        break
      }
      
      let nextStep = visitUse(ofAddress: use, path: path,
                              isLeaf: maybeNext == nil)
      
      switch nextStep {
      case .stopWalk:
        break
      case .abortWalk:
        return true
      case .continueWalk:
        if let (addr, p) = maybeNext,
          walkDown(address: addr, path: p) {
          return true
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

protocol UseDefWalker {
  mutating
  func shouldRecomputeUp(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
  
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                isRoot: Bool) -> WalkResult
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath,
                isRoot: Bool) -> WalkResult
}

extension UseDefWalker {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                isRoot: Bool)  -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath, isRoot: Bool) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `DefUseWalker.walkDown(value:`
  mutating
  func walkUp(value def: Value, path: SmallProjectionPath) -> Bool {
    var current: (value: Value, path: SmallProjectionPath) = (def, path)
    
    while true {
      
      var maybeNext: (Value, SmallProjectionPath)?
      
      let (value, path) = current
      switch value {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          maybeNext = (str.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return visitAndWalkUp(value: value, path: path, operands: str.operands, newPath: path)
        }
      case let t as TupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          maybeNext = (t.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return visitAndWalkUp(value: value, path: path, operands: t.operands, newPath: path)
        }
      case let e as EnumInst:
        if let newPath = path.popIfMatches(.enumCase, index: e.caseIndex),
           let operand = e.operand {
          maybeNext = (operand, newPath)
        }
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        maybeNext = (se.operand, path.push(.structField, index: se.fieldIndex))
      case let te as TupleExtractInst:
        maybeNext = (te.operand, path.push(.tupleField, index: te.fieldIndex))
      case let ued as UncheckedEnumDataInst:
        maybeNext = (ued.operand, path.push(.enumCase, index: ued.caseIndex))
      // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
      case let mvr as MultipleValueInstructionResult
        where mvr.instruction is DestructureStructInst:
        let ds = mvr.instruction as! DestructureStructInst
        maybeNext = (ds.operand, path.push(.structField, index: mvr.index))
      case let mvr as MultipleValueInstructionResult
        where mvr.instruction is DestructureTupleInst:
        let dt = mvr.instruction as! DestructureTupleInst
        maybeNext = (dt.operand, path.push(.tupleField, index: mvr.index))
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        maybeNext = ((value as! Instruction).operands[0].value, path)
      case let mvr as MultipleValueInstructionResult
        where mvr.instruction is BeginCOWMutationInst:
        let bcm = (mvr.instruction as! BeginCOWMutationInst)
        maybeNext = (bcm.operand, path)
      // MARK: Non-Address Block Arguments
      case let arg as BlockArgument:
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
              maybeNext = (se.enumOp, path.push(.enumCase, index: caseIdx))
            } else {
              // NOTE: ("EscapeInfo returns .abortWalk (isEscaping)")
              // here instead we leave maybeNext to be nil so the client
              // can handle this as root.
            }
          case is TryApplyInst:
            fatalError("Remember to handle TryApplyInst in clients")
          default:
            break
          }
        }
      default:
        break
      }
      
      let nextStep = visitDef(ofValue: value, path: path,
                              isRoot: maybeNext == nil)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if let (val, p) = maybeNext {
          current = (val, p)
        }
      }
    }
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `DefUseWalker.walkDown(address:`
  mutating
  func walkUp(address def: Value, path: SmallProjectionPath) -> Bool {
    var current = (def, path)
    
    while true {
      var maybeNext: (Value, SmallProjectionPath)?
      
      let (addr, p) = current
      switch addr {
      // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        maybeNext = (sea.operand, path.push(.structField, index: sea.fieldIndex))
      case let tea as TupleElementAddrInst:
        maybeNext = (tea.operand, path.push(.tupleField, index: tea.fieldIndex))
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = addr as! EnumInst
        maybeNext = (ei.operand, path.push(.enumCase, index: ei.caseIndex))
      // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
           is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        maybeNext = ((addr as! Instruction).operands[0].value, path)
      case let mdi as MarkDependenceInst:
        maybeNext = (mdi.operands[0].value, path)
      default:
        break
      }
      
      let nextStep = visitDef(ofAddress: addr, path: p,
                              isRoot: maybeNext == nil)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if let (nextAddr, nextPath) = maybeNext {
          current = (nextAddr, nextPath)
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
