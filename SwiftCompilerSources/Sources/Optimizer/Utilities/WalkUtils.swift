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

enum WalkerVisitKind {
  case interiorValue
  case terminalValue
  case unmatchedPath
}

protocol DefUseWalker {
  mutating
  func shouldRecomputeDown(value def: Value, path: SmallProjectionPath) -> SmallProjectionPath?
  
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult
}

extension DefUseWalker {
  mutating
  func visitUse(ofValue operand: Operand, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitUse(ofAddress operand: Operand, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `UseDefWalker.walkUp(value:`
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath) -> Bool {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      let abortWalk: Bool
      
      let instruction = operand.instruction
      switch instruction {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        abortWalk = visitAndWalkDown(value: operand, path: path,
                                   walkTo: (str, path.push(.structField, index: operand.index)),
                                   next: .interiorValue)
      case let t as TupleInst:
        abortWalk = visitAndWalkDown(value: operand, path: path,
                                   walkTo: (t, path.push(.tupleField, index: operand.index)),
                                   next: .interiorValue)
      case let e as EnumInst:
        abortWalk = visitAndWalkDown(value: operand, path: path,
                                   walkTo: (e, path.push(.enumCase, index: e.caseIndex)),
                                   next: .interiorValue)
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          abortWalk = visitAndWalkDown(value: operand, path: path,
                                     walkTo: (se, newPath),
                                     next: .interiorValue)
        } else {
          abortWalk = visitUse(ofValue: operand, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let te as TupleExtractInst:
        if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
          abortWalk = visitAndWalkDown(value: operand, path: path,
                                     walkTo: (te, newPath), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofValue: operand, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let ued as UncheckedEnumDataInst:
        if let newPath = path.popIfMatches(.enumCase, index: ued.caseIndex) {
          abortWalk = visitAndWalkDown(value: operand, path: path,
                                     walkTo: (ued, newPath), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofValue: operand, path: path, kind: .unmatchedPath) == .abortWalk
        }
      // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          abortWalk = visitAndWalkDown(value: operand, path: path,
                                     walkTo: (ds.results[index], newPath),
                                     next: .interiorValue)
        } else if path.topMatchesAnyValueField {
          abortWalk = handleDestructureAnyValueField(operand, path: path,
                                                   values: instruction.results, newPath: path)
        } else {
          abortWalk = visitUse(ofValue: operand, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          abortWalk = visitAndWalkDown(value: operand, path: path,
                                     walkTo: (dt.results[index], newPath), next: .interiorValue)
        } else if path.topMatchesAnyValueField {
          abortWalk = handleDestructureAnyValueField(operand, path: path,
                                                   values: instruction.results, newPath: path)
        } else {
          abortWalk = visitUse(ofValue: operand, path: path, kind: .unmatchedPath) == .abortWalk
        }
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        abortWalk = visitAndWalkDown(value: operand, path: path,
                                   walkTo: (instruction as! SingleValueInstruction, path),
                                   next: .interiorValue)
      case let bcm as BeginCOWMutationInst:
        abortWalk = visitAndWalkDown(value: operand, path: path,
                                   walkTo: (bcm.bufferResult, path), next: .interiorValue)
      // MARK: Non-Address Branching Instructions
      case let br as BranchInst:
        let visitResult = visitUse(ofValue: operand, path: path, kind: .interiorValue)
        switch visitResult {
        case .stopWalk:
          continue
        case .abortWalk:
          return true
        case .continueWalk:
          let val = br.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            abortWalk = walkDown(value: val, path: path)
          } else {
            continue
          }
        }
      case let cbr as CondBranchInst:
        assert(operand.index != 0, "should not visit trivial non-address values")
        let visitResult = visitUse(ofValue: operand, path: path, kind: .interiorValue)
        switch visitResult {
        case .stopWalk:
          continue
        case .abortWalk:
          return true
        case .continueWalk:
          let val = cbr.getArgument(for: operand)
          if let path = shouldRecomputeDown(value: val, path: path) {
            abortWalk = walkDown(value: val, path: path)
          } else {
            continue
          }
        }
      default:
          let visitResult = visitUse(ofValue: operand, path: path, kind: .terminalValue)
          switch visitResult {
          case .stopWalk:
            continue
          case .abortWalk:
            return true
          case .continueWalk:
            continue
          }
      }
      
      if abortWalk {
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
      
      let abortWalk: Bool
      
      let instruction = use.instruction
      switch instruction {
      // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
          abortWalk = visitAndWalkDown(address: use, path: path,
                                     walkTo: (sea, newPath), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofAddress: use, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let tea as TupleElementAddrInst:
        if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
          abortWalk = visitAndWalkDown(address: use, path: path,
                                     walkTo: (tea, newPath), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofAddress: use, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = instruction as! EnumInst
        if let newPath = path.popIfMatches(.enumCase, index: ei.caseIndex) {
          abortWalk = visitAndWalkDown(address: use, path: path,
                                     walkTo: (ei, newPath), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofAddress: use, path: path, kind: .unmatchedPath) == .abortWalk
        }
      // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
           is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        abortWalk = visitAndWalkDown(address: use, path: path,
                                   walkTo: (instruction as! SingleValueInstruction, path), next: .interiorValue)
      case let mdi as MarkDependenceInst:
        if use.index == 0 {
          abortWalk = visitAndWalkDown(address: use, path: path,
                                     walkTo: (mdi, path), next: .interiorValue)
        } else {
          abortWalk = visitUse(ofAddress: use, path: path, kind: .terminalValue /* conservative */) == .abortWalk
        }
      default:
        abortWalk = visitUse(ofAddress: use, path: path, kind: .terminalValue) == .abortWalk
      }
      
      if abortWalk {
        return true
      }
    }
    return false
  }
  
  private mutating
  func visitAndWalkDown(
    value operand: Operand, path: SmallProjectionPath,
    walkTo: (value: Value, path: SmallProjectionPath), next: WalkerVisitKind
  ) -> Bool {
    let visitResult = visitUse(ofValue: operand, path: path, kind: next)
    switch visitResult {
    case .stopWalk:
      return false
    case .abortWalk:
      return true
    case .continueWalk:
      return walkDown(value: walkTo.value, path: walkTo.path)
    }
  }
  
  private mutating
  func visitAndWalkDown(
    address operand: Operand, path: SmallProjectionPath,
    walkTo: (value: Value, path: SmallProjectionPath), next: WalkerVisitKind
  ) -> Bool {
    let visitResult = visitUse(ofAddress: operand, path: path, kind: next)
    switch visitResult {
    case .stopWalk:
      return false
    case .abortWalk:
      return true
    case .continueWalk:
      return walkDown(address: walkTo.value, path: walkTo.path)
    }
  }
  
  private mutating
  func handleDestructureAnyValueField(_ operand: Operand, path: SmallProjectionPath, values: Instruction.Results,
                        newPath: SmallProjectionPath) -> Bool {
    let maybeContinue = visitUse(ofValue: operand, path: path, kind: .interiorValue)
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
                kind: WalkerVisitKind) -> WalkResult
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult
}

extension UseDefWalker {
  mutating
  func visitDef(ofValue value: Value, path: SmallProjectionPath,
                kind: WalkerVisitKind)  -> WalkResult {
    return .continueWalk
  }
  
  mutating
  func visitDef(ofAddress: Value, path: SmallProjectionPath,
                kind: WalkerVisitKind) -> WalkResult {
    return .continueWalk
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `DefUseWalker.walkDown(value:`
  mutating
  func walkUp(value def: Value, path: SmallProjectionPath) -> Bool {
    var current: (value: Value, path: SmallProjectionPath) = (def, path)
    
    while true {
      
      let next: (value: Value, path: SmallProjectionPath)
      
      let (value, path) = current
      switch value {
      // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          next = (str.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return walkAggregateInstUp(str, path: path)
        } else {
          return visitDef(ofValue: value, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let t as TupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          next = (t.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return walkAggregateInstUp(t, path: path)
        } else {
          return visitDef(ofValue: value, path: path, kind: .unmatchedPath) == .abortWalk
        }
      case let e as EnumInst:
        if let newPath = path.popIfMatches(.enumCase, index: e.caseIndex),
           let operand = e.operand {
          next = (operand, newPath)
        } else {
          return visitDef(ofValue: value, path: path, kind: .unmatchedPath) == .abortWalk
        }
      // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        next = (se.operand, path.push(.structField, index: se.fieldIndex))
      case let te as TupleExtractInst:
        next = (te.operand, path.push(.tupleField, index: te.fieldIndex))
      case let ued as UncheckedEnumDataInst:
        next = (ued.operand, path.push(.enumCase, index: ued.caseIndex))
      case let mvr as MultipleValueInstructionResult:
        // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
        if let ds = mvr.instruction as? DestructureStructInst {
          next = (ds.operand, path.push(.structField, index: mvr.index))
        } else if let dt = mvr.instruction as? DestructureTupleInst {
          next = (dt.operand, path.push(.tupleField, index: mvr.index))
        } else if let bcm = mvr.instruction as? BeginCOWMutationInst {
          // MARK: Non-Address to Non-Address Forwarding Instruction
          next = (bcm.operand, path)
        } else {
          return visitDef(ofValue: value, path: path, kind: .terminalValue) == .abortWalk
        }
      // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
           is BeginBorrowInst, is CopyValueInst,
           is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
           is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        next = ((value as! Instruction).operands[0].value, path)
      // MARK: Non-Address Block Arguments
      case let arg as BlockArgument where arg.isPhiArgument:
        let nextStep = visitDef(ofValue: arg, path: path, kind: .interiorValue)
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
        return visitDef(ofValue: value, path: path, kind: .terminalValue) == .abortWalk
      }
      
      let nextStep = visitDef(ofValue: value, path: path, kind: .interiorValue)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        current = (next.value, next.path)
      }
    }
  }
  
  /// - Returns: true if the walk was aborted
  // Note: keep it symmetric to `DefUseWalker.walkDown(address:`
  mutating
  func walkUp(address def: Value, path: SmallProjectionPath) -> Bool {
    var current = (def, path)
    
    while true {
      let next: (addr: Value, path: SmallProjectionPath)
      
      let (addr, p) = current
      switch addr {
      // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        next = (sea.operand, path.push(.structField, index: sea.fieldIndex))
      case let tea as TupleElementAddrInst:
        next = (tea.operand, path.push(.tupleField, index: tea.fieldIndex))
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = addr as! EnumInst
        next = (ei.operand, path.push(.enumCase, index: ei.caseIndex))
      // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
           is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        next = ((addr as! Instruction).operands[0].value, path)
      case let mdi as MarkDependenceInst:
        next = (mdi.operands[0].value, path)
      default:
        return visitDef(ofAddress: addr, path: p, kind: .terminalValue) == .abortWalk
      }
      
      let nextStep = visitDef(ofAddress: addr, path: p, kind: .interiorValue)
      
      switch nextStep {
      case .stopWalk:
        return false
      case .abortWalk:
        return true
      case .continueWalk:
        current = (next.addr, next.path)
      }
    }
  }
  
  private mutating
  func walkAggregateInstUp(_ inst: SingleValueInstruction, path: SmallProjectionPath) -> Bool {
    let nextStep = visitDef(ofValue: inst, path: path, kind: .interiorValue)
    switch nextStep {
    case .abortWalk:
      return true
    case .stopWalk:
      return false
    case .continueWalk:
      for op in inst.operands {
        if let path = shouldRecomputeUp(value: op.value, path: path),
           walkUp(value: op.value, path: path) {
          return true
        }
      }
      return false
    }
  }
}
