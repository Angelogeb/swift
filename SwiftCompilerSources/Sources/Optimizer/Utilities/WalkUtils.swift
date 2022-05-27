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

enum WalkerNextStep {
  case canContinue
  case unmatchedInst
  case unmatchedPath
}

protocol DefUseWalker {
  mutating
  func shouldRecomputeDown(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
  
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath,
                next: WalkerNextStep) -> WalkResult
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                next: WalkerNextStep) -> WalkResult
}

extension DefUseWalker {
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath,
                next: WalkerNextStep) -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                next: WalkerNextStep) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `UseDefWalker.walkUp(value:`
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      let aborted: Bool
      
      let instruction = operand.instruction
      switch instruction {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        aborted = visitAndWalkDown(value: operand, path: path,
                                  toWalk: (str, path.push(.structField, index: operand.index)),
                                   next: .canContinue)
      case let t as TupleInst:
        aborted = visitAndWalkDown(value: operand, path: path,
                                   toWalk: (t, path.push(.tupleField, index: operand.index)),
                                   next: .canContinue)
      case let e as EnumInst:
        aborted = visitAndWalkDown(value: operand, path: path,
                                   toWalk: (e, path.push(.enumCase, index: e.caseIndex)),
                                   next: .canContinue)
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: (se, newPath),
                                     next: .canContinue)
        } else {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      case let te as TupleExtractInst:
        if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: (te, newPath), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      case let ued as UncheckedEnumDataInst:
        if let newPath = path.popIfMatches(.enumCase, index: ued.caseIndex) {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: (ued, newPath), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: (ds.results[index], newPath),
                                     next: .canContinue)
        } else if path.topMatchesAnyValueField {
          aborted = handleDestructureAnyValueField(operand, path: path,
                                                   values: instruction.results, newPath: path)
        } else {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: (dt.results[index], newPath), next: .canContinue)
        } else if path.topMatchesAnyValueField {
          aborted = handleDestructureAnyValueField(operand, path: path,
                                                   values: instruction.results, newPath: path)
        } else {
          aborted = visitAndWalkDown(value: operand, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        aborted = visitAndWalkDown(value: operand, path: path,
                                   toWalk: (instruction as! SingleValueInstruction, path),
                                   next: .canContinue)
      case let bcm as BeginCOWMutationInst:
        aborted = visitAndWalkDown(value: operand, path: path,
                                   toWalk: (bcm.bufferResult, path), next: .canContinue)
      // MARK: Non-Address Branching Instructions
      case let br as BranchInst:
        let visitResult = visitUse(ofValue: operand, path: path, next: .canContinue)
        switch visitResult {
        case .stopWalk:
          continue
        case .abortWalk:
          return true
        case .continueWalk:
          let val = br.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            aborted = walkDown(value: val, path: path)
          } else {
            continue
          }
        }
      case let cbr as CondBranchInst:
        assert(operand.index != 0, "should not visit trivial non-address values")
        let visitResult = visitUse(ofValue: operand, path: path, next: .canContinue)
        switch visitResult {
        case .stopWalk:
          continue
        case .abortWalk:
          return true
        case .continueWalk:
          let val = cbr.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            aborted = walkDown(value: val, path: path)
          } else {
            continue
          }
        }
      default:
          let visitResult = visitUse(ofValue: operand, path: path, next: .unmatchedInst)
          switch visitResult {
          case .stopWalk:
            continue
          case .abortWalk:
            return true
          case .continueWalk:
            continue
          }
      }
      
      if aborted {
        return true
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
      
      let aborted: Bool
      
      let instruction = use.instruction
      switch instruction {
      // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: (sea, newPath), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      case let tea as TupleElementAddrInst:
        if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: (tea, newPath), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = instruction as! EnumInst
        if let newPath = path.popIfMatches(.enumCase, index: ei.caseIndex) {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: (ei, newPath), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: nil, next: .unmatchedPath)
        }
      // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
           is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        aborted = visitAndWalkDown(address: use, path: path,
                                   toWalk: (instruction as! SingleValueInstruction, path), next: .canContinue)
      case let mdi as MarkDependenceInst:
        if use.index == 0 {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: (mdi, path), next: .canContinue)
        } else {
          aborted = visitAndWalkDown(address: use, path: path,
                                     toWalk: nil, next: .unmatchedInst /* conservative */)
        }
      default:
        aborted = visitAndWalkDown(address: use, path: path,
                                   toWalk: nil, next: .unmatchedInst)
      }
      
      if aborted {
        return true
      }
    }
    return false
  }
  
  private mutating
  func visitAndWalkDown(
    value operand: Operand, path: SmallProjectionPath,
    toWalk: (value: Value, path: SmallProjectionPath)?, next: WalkerNextStep
  ) -> Bool {
    precondition(!(toWalk == nil && next == .canContinue), "Inconsistent arguments")
    let visitResult = visitUse(ofValue: operand, path: path, next: next)
    switch visitResult {
    case .stopWalk:
      return false
    case .abortWalk:
      return true
    case .continueWalk:
      if let next = toWalk {
        return walkDown(value: next.value, path: next.path)
      }
    }
    return false
  }
  
  private mutating
  func visitAndWalkDown(
    address operand: Operand, path: SmallProjectionPath,
    toWalk: (value: Value, path: SmallProjectionPath)?, next: WalkerNextStep
  ) -> Bool {
    precondition(!(toWalk == nil && next == .canContinue), "Inconsistent arguments")
    let visitResult = visitUse(ofAddress: operand, path: path, next: next)
    switch visitResult {
    case .stopWalk:
      return false
    case .abortWalk:
      return true
    case .continueWalk:
      if let next = toWalk {
        return walkDown(address: next.value, path: next.path)
      }
    }
    return false
  }
  
  private mutating
  func handleDestructureAnyValueField(_ operand: Operand, path: SmallProjectionPath, values: Instruction.Results,
                        newPath: SmallProjectionPath) -> Bool {
    let maybeContinue = visitUse(ofValue: operand, path: path, next: .canContinue)
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
                isRoot: WalkerNextStep) -> WalkResult
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath,
                isRoot: WalkerNextStep) -> WalkResult
}

extension UseDefWalker {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                isRoot: WalkerNextStep)  -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath,
                isRoot: WalkerNextStep) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `DefUseWalker.walkDown(value:`
  mutating
  func walkUp(value def: Value, path: SmallProjectionPath) -> Bool {
    var current: (value: Value, path: SmallProjectionPath) = (def, path)
    
    while true {
      
      let maybeNext: (Value, SmallProjectionPath)?
      let nextArg: WalkerNextStep
      
      let (value, path) = current
      switch value {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          maybeNext = (str.operands[index].value, newPath)
          nextArg = .canContinue
        } else if path.topMatchesAnyValueField {
          return handleAnyValueFieldUp(value: value, path: path, operands: str.operands)
        } else {
          maybeNext = nil
          nextArg = .unmatchedPath
        }
      case let t as TupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          maybeNext = (t.operands[index].value, newPath)
          nextArg = .canContinue
        } else if path.topMatchesAnyValueField {
          return handleAnyValueFieldUp(value: value, path: path, operands: t.operands)
        } else {
          maybeNext = nil
          nextArg = .unmatchedPath
        }
      case let e as EnumInst:
        if let newPath = path.popIfMatches(.enumCase, index: e.caseIndex),
           let operand = e.operand {
          maybeNext = (operand, newPath)
          nextArg = .canContinue
        } else {
          maybeNext = nil
          nextArg = .unmatchedPath
        }
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        maybeNext = (se.operand, path.push(.structField, index: se.fieldIndex))
        nextArg = .canContinue
      case let te as TupleExtractInst:
        maybeNext = (te.operand, path.push(.tupleField, index: te.fieldIndex))
        nextArg = .canContinue
      case let ued as UncheckedEnumDataInst:
        maybeNext = (ued.operand, path.push(.enumCase, index: ued.caseIndex))
        nextArg = .canContinue
      case let mvr as MultipleValueInstructionResult:
        // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
        if let ds = mvr.instruction as? DestructureStructInst {
          maybeNext = (ds.operand, path.push(.structField, index: mvr.index))
          nextArg = .canContinue
        } else if let dt = mvr.instruction as? DestructureTupleInst {
          maybeNext = (dt.operand, path.push(.tupleField, index: mvr.index))
          nextArg = .canContinue
        } else if let bcm = mvr.instruction as? BeginCOWMutationInst {
          // MARK: Non-Address to Non-Address Forwarding Instruction
          maybeNext = (bcm.operand, path)
          nextArg = .canContinue
        } else {
          maybeNext = nil
          nextArg = .unmatchedInst
        }
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        maybeNext = ((value as! Instruction).operands[0].value, path)
        nextArg = .canContinue
      // MARK: Non-Address Block Arguments
      case let arg as BlockArgument where arg.isPhiArgument:
        let nextStep = visitDef(ofValue: arg, path: path, isRoot: .canContinue)
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
      default:
        maybeNext = nil
        nextArg = .unmatchedInst
      }
      
      let nextStep = visitDef(ofValue: value, path: path, isRoot: nextArg)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if let (val, p) = maybeNext {
          current = (val, p)
        } else {
          return false
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
      let maybeNext: (Value, SmallProjectionPath)?
      
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
        maybeNext = nil
      }
      
      let nextStep = visitDef(ofAddress: addr, path: p,
                              isRoot: maybeNext == nil ? .unmatchedInst : .canContinue)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        if let (nextAddr, nextPath) = maybeNext {
          current = (nextAddr, nextPath)
        } else {
          return false
        }
      }
    }
  }
  
  private mutating
  func handleAnyValueFieldUp(value def: Value, path: SmallProjectionPath, operands: OperandArray) -> Bool {
    let nextStep = visitDef(ofValue: def, path: path, isRoot: .canContinue)
    switch nextStep {
    case .abortWalk:
      return true
    case .stopWalk:
      return false
    case .continueWalk:
      for op in operands {
        if let path = shouldRecomputeUp(value: op.value, path: path),
           walkUp(value: op.value, path: path) {
          return true
        }
      }
      return false
    }
  }
}
