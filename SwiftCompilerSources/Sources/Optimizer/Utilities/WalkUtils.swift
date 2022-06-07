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


protocol HasResult {
  var result: WalkResult { get }
  
  func with(result: WalkResult) -> Self
}

protocol HasState {
  associatedtype State : HasResult
}

protocol UseVisitor : HasState {
  mutating
  func visitUse(operand: Operand, path: SmallProjectionPath, kind: WalkerVisitKind, state: State) -> State
  
  mutating
  func shouldRecomputeDown(def: Value, path: SmallProjectionPath, state: State) -> (SmallProjectionPath, State)?
}

protocol DefVisitor : HasState {
  mutating
  func visitDef(object: Value, path: SmallProjectionPath, kind: WalkerVisitKind, state: State) -> State
  
  mutating
  func shouldRecomputeUp(def: Value, path: SmallProjectionPath, state: State) -> (SmallProjectionPath, State)?
}


extension UseVisitor {
  mutating
  func walkDown(value def: Value, path: SmallProjectionPath, state: State) -> State {
    for operand in def.uses {
      if operand.isTypeDependent { continue }
      
      let resultState: State
      
      let instruction = operand.instruction
      switch instruction {
        // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        resultState = visitAndWalkDown(value: operand, path: path,
                                       walkTo: (str, path.push(.structField, index: operand.index)),
                                       next: .interiorValue, state: state)
      case let t as TupleInst:
        resultState = visitAndWalkDown(value: operand, path: path,
                                       walkTo: (t, path.push(.tupleField, index: operand.index)),
                                       next: .interiorValue, state: state)
      case let e as EnumInst:
        resultState = visitAndWalkDown(value: operand, path: path,
                                       walkTo: (e, path.push(.enumCase, index: e.caseIndex)),
                                       next: .interiorValue, state: state)
        // MARK: Non-Address to Non-Address Projections
      case let se as StructExtractInst:
        if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
          resultState = visitAndWalkDown(value: operand, path: path,
                                         walkTo: (se, newPath),
                                         next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: operand, path: path, kind: .unmatchedPath, state: state)
        }
      case let te as TupleExtractInst:
        if let newPath = path.popIfMatches(.tupleField, index: te.fieldIndex) {
          resultState = visitAndWalkDown(value: operand, path: path,
                                         walkTo: (te, newPath), next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: operand, path: path, kind: .unmatchedPath, state: state)
        }
      case let ued as UncheckedEnumDataInst:
        if let newPath = path.popIfMatches(.enumCase, index: ued.caseIndex) {
          resultState = visitAndWalkDown(value: operand, path: path,
                                         walkTo: (ued, newPath), next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: operand, path: path, kind: .unmatchedPath, state: state)
        }
        // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
      case let ds as DestructureStructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          resultState = visitAndWalkDown(value: operand, path: path,
                                         walkTo: (ds.results[index], newPath),
                                         next: .interiorValue, state: state)
        } else if path.topMatchesAnyValueField {
          resultState = handleDestructureAnyValueField(value: operand, path: path, values: ds.results, state: state)
        } else {
          resultState = visitUse(operand: operand, path: path, kind: .unmatchedPath, state: state)
        }
      case let dt as DestructureTupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          resultState = visitAndWalkDown(value: operand, path: path,
                                         walkTo: (dt.results[index], newPath),
                                         next: .interiorValue, state: state)
        } else if path.topMatchesAnyValueField {
          resultState = handleDestructureAnyValueField(value: operand, path: path, values: dt.results, state: state)
        } else {
          resultState = visitUse(operand: operand, path: path, kind: .unmatchedPath, state: state)
        }
        // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
        is BeginBorrowInst, is CopyValueInst,
        is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
        is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        resultState = visitAndWalkDown(value: operand, path: path,
                                       walkTo: (instruction as! SingleValueInstruction, path),
                                       next: .interiorValue, state: state)
        // MARK: Non-Address Branching Instructions
      case let br as BranchInst:
        let visitState = visitUse(operand: operand, path: path, kind: .interiorValue, state: state)
        switch visitState.result {
        case .stopWalk:
          continue
        case .abortWalk:
          return visitState
        case .continueWalk:
          let val = br.getArgument(for: operand)
          if let (newPath, newState) = shouldRecomputeDown(def: val, path: path, state: visitState) {
            resultState = walkDown(value: val, path: newPath, state: newState)
          } else {
            continue
          }
        }
      case let cbr as CondBranchInst:
        assert(operand.index != 0, "should not visit trivial non-address values")
        let visitState = visitUse(operand: operand, path: path, kind: .interiorValue, state: state)
        switch visitState.result {
        case .stopWalk:
          continue
        case .abortWalk:
          return visitState
        case .continueWalk:
          let val = cbr.getArgument(for: operand)
          if let (newPath, newState) = shouldRecomputeDown(def: val, path: path, state: visitState) {
            resultState = walkDown(value: val, path: newPath, state: newState)
          } else {
            continue
          }
        }
      case let bcm as BeginCOWMutationInst:
        resultState = visitAndWalkDown(value: operand, path: path,
                                       walkTo: (bcm.bufferResult, path),
                                       next: .interiorValue, state: state)
      default:
        let visitResult = visitUse(operand: operand, path: path, kind: .terminalValue, state: state)
        switch visitResult.result {
        case .abortWalk:
          return visitResult
        default:
          continue
        }
      }
      
      if resultState.result == .abortWalk {
        return resultState
      }
    }
    
    return state.with(result: .stopWalk)
  }
  
  mutating
  func walkDown(address def: Value, path: SmallProjectionPath, state: State) -> State {
    for use in def.uses {
      if use.isTypeDependent { continue }
      
      let resultState: State
      
      let instruction = use.instruction
      switch instruction {
        // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
          resultState = visitAndWalkDown(address: use, path: path, walkTo: (sea, newPath),
                                         next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: use, path: path, kind: .unmatchedPath, state: state)
        }
      case let tea as TupleElementAddrInst:
        if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
          resultState = visitAndWalkDown(address: use, path: path, walkTo: (tea, newPath),
                                         next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: use, path: path, kind: .unmatchedPath, state: state)
        }
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = instruction as! EnumInst
        if let newPath = path.popIfMatches(.enumCase, index: ei.caseIndex) {
          resultState = visitAndWalkDown(address: use, path: path, walkTo: (ei, newPath),
                                         next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: use, path: path, kind: .unmatchedPath, state: state)
        }
        // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
        is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        resultState = visitAndWalkDown(address: use, path: path, walkTo: (instruction as! SingleValueInstruction, path),
                                       next: .interiorValue, state: state)
      case let mdi as MarkDependenceInst:
        if use.index == 0 {
          resultState = visitAndWalkDown(address: use, path: path, walkTo: (mdi, path),
                                         next: .interiorValue, state: state)
        } else {
          resultState = visitUse(operand: use, path: path, kind: .terminalValue /* conservative */, state: state)
        }
      default:
        resultState = visitUse(operand: use, path: path, kind: .terminalValue, state: state)
      }
      
      if resultState.result == .abortWalk {
        return resultState
      }
    }
    return state.with(result: .stopWalk)
  }
  
  private mutating
  func handleDestructureAnyValueField(value: Operand, path: SmallProjectionPath,
                                      values: Instruction.Results,
                                      state: State) -> State {
    let visitState = visitUse(operand: value, path: path, kind: .interiorValue, state: state)
    switch visitState.result {
    case .continueWalk:
      for result in values {
        if let (newPath, newState) = shouldRecomputeDown(def: result, path: path, state: visitState) {
          let walkState = walkDown(value: result, path: newPath, state: newState)
          switch walkState.result {
          case .abortWalk:
            return walkState
          default:
            break
          }
        }
      }
      return state.with(result: .continueWalk)
    default:
      return state.with(result: .continueWalk)
    }
  }
  
  private mutating
  func visitAndWalkDown(value: Operand, path: SmallProjectionPath,
                        walkTo: (value: Value, path: SmallProjectionPath),
                        next: WalkerVisitKind, state: State) -> State {
    let state = visitUse(operand: value, path: path, kind: next, state: state)
    switch state.result {
    case .continueWalk:
      return walkDown(value: walkTo.value, path: walkTo.path, state: state)
    default:
      return state
    }
  }
  
  private mutating
  func visitAndWalkDown(
    address operand: Operand, path: SmallProjectionPath,
    walkTo: (value: Value, path: SmallProjectionPath), next: WalkerVisitKind, state: State) -> State {
      let newState = visitUse(operand: operand, path: path, kind: next, state: state)
      switch newState.result {
      case .continueWalk:
        return walkDown(address: walkTo.value, path: walkTo.path, state: newState)
      default:
        return newState
      }
    }
}


extension DefVisitor {
  
  mutating
  func walkUp(value def: Value, path: SmallProjectionPath, state: State) -> State {
    var current: (value: Value, path: SmallProjectionPath, state: State) = (def, path, state)
    
    while true {
      
      let next: (value: Value, path: SmallProjectionPath)
      
      let (value, path, state) = current
      switch value {
        // MARK: (trivially Non-Address to Non-Address) Constructions
      case let str as StructInst:
        if let (index, newPath) = path.pop(kind: .structField) {
          next = (str.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return walkAggregateInstUp(str, path: path, state: state)
        } else {
          return visitDef(object: value, path: path, kind: .unmatchedPath, state: state)
        }
      case let t as TupleInst:
        if let (index, newPath) = path.pop(kind: .tupleField) {
          next = (t.operands[index].value, newPath)
        } else if path.topMatchesAnyValueField {
          return walkAggregateInstUp(t, path: path, state: state)
        } else {
          return visitDef(object: value, path: path, kind: .unmatchedPath, state: state)
        }
      case let e as EnumInst:
        if let newPath = path.popIfMatches(.enumCase, index: e.caseIndex),
           let operand = e.operand {
          next = (operand, newPath)
        } else {
          return visitDef(object: value, path: path, kind: .unmatchedPath, state: state)
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
          return visitDef(object: value, path: path, kind: .terminalValue, state: state)
        }
        // MARK: Non-Address to Non-Address Forwarding Instructions
      case is InitExistentialRefInst, is OpenExistentialRefInst,
        is BeginBorrowInst, is CopyValueInst,
        is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
        is RefToBridgeObjectInst, is BridgeObjectToRefInst:
        next = ((value as! Instruction).operands[0].value, path)
        // MARK: Non-Address Block Arguments
      case let arg as BlockArgument where arg.isPhiArgument:
        let visitState = visitDef(object: arg, path: path, kind: .interiorValue, state: state)
        switch visitState.result {
        case .continueWalk:
          for incoming in arg.incomingPhiValues {
            if let (newPath, newState) = shouldRecomputeUp(def: incoming, path: path, state: state) {
              let walkUpState = walkUp(value: incoming, path: newPath, state: newState)
              if walkUpState.result == .abortWalk {
                return walkUpState
              }
            }
          }
          return visitState
        default:
          return visitState
        }
      default:
        return visitDef(object: value, path: path, kind: .terminalValue, state: state)
      }
      
      let visitState = visitDef(object: value, path: path, kind: .interiorValue, state: state)
      
      switch visitState.result {
      case .continueWalk:
        current = (next.value, next.path, visitState)
      default:
        return visitState
      }
    }
  }
  
  mutating
  func walkUp(address def: Value, path: SmallProjectionPath, state: State) -> State {
    var current = (def, path, state)
    
    while true {
      let next: (def: Value, path: SmallProjectionPath)
      
      let (def, path, state) = current
      switch def {
        // MARK: Address to Address Projections
      case let sea as StructElementAddrInst:
        next = (sea.operand, path.push(.structField, index: sea.fieldIndex))
      case let tea as TupleElementAddrInst:
        next = (tea.operand, path.push(.tupleField, index: tea.fieldIndex))
      case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
        let ei = def as! EnumInst
        next = (ei.operand, path.push(.enumCase, index: ei.caseIndex))
        // MARK: Address to Address Forwarding Instructions
      case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
        is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
        next = ((def as! Instruction).operands[0].value, path)
      case let mdi as MarkDependenceInst:
        next = (mdi.operands[0].value, path)
      default:
        return visitDef(object: def, path: path, kind: .terminalValue, state: state)
      }
      
      let newState = visitDef(object: def, path: path, kind: .interiorValue, state: state)
      
      switch newState.result {
      case .continueWalk:
        current = (next.def, next.path, newState)
      default:
        return newState
      }
    }
  }
  
  private mutating
  func walkAggregateInstUp(_ inst: SingleValueInstruction, path: SmallProjectionPath, state: State) -> State {
    let visitState = visitDef(object: inst, path: path, kind: .interiorValue, state: state)
    switch visitState.result {
    case .continueWalk:
      for op in inst.operands {
        if let (newPath, newState) = shouldRecomputeUp(def: op.value, path: path, state: visitState) {
          let walkUpState = walkUp(value: op.value, path: newPath, state: newState)
          if walkUpState.result == .abortWalk {
            return walkUpState
          }
        }
      }
      return visitState
    default:
      return visitState
    }
  }
  
}
