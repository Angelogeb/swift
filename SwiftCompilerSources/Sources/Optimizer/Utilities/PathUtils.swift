//===--- PathUtils.swift - Utilities for use-def def-use paths ------------===//
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

enum ResultPath {
  case unmatchedInstruction
  case unmatchedPath
  case some(Value, SmallProjectionPath)
}

// walkdown
func resultPath(operand: Operand, path: SmallProjectionPath) -> ResultPath {
  let instruction = operand.instruction
  switch instruction {
  // MARK: (trivially Non-Address to Non-Address) Constructions
  case let str as StructInst:
    return .some(str, path.push(.structField, index: operand.index))
  case let t as TupleInst:
    return .some(t, path.push(.tupleField, index: operand.index))
  case let e as EnumInst:
    return .some(e, path.push(.enumCase, index: e.caseIndex))
  // MARK: Non-Address to Non-Address Projections
  case let se as StructExtractInst:
    if let newPath = path.popIfMatches(.structField, index: se.fieldIndex) {
      return .some(se, newPath)
    }
  case let ued as UncheckedEnumDataInst:
    if let newPath = path.popIfMatches(.enumCase, index: ued.caseIndex) {
      return .some(ued, newPath)
    }
  // MARK: Non-Address to Address Projections
  case let rta as RefTailAddrInst:
    if let newPath = path.popIfMatches(.tailElements) {
      return .some(rta, newPath)
    }
  case let rea as RefElementAddrInst:
    if let newPath = path.popIfMatches(.classField, index: rea.fieldIndex) {
      return .some(rea, newPath)
    }
  case let pb as ProjectBoxInst:
    if let newPath = path.popIfMatches(.classField, index: pb.fieldIndex) {
      return .some(pb, newPath)
    }
  // MARK: Address to Address Projections
  case let sea as StructElementAddrInst:
    if let newPath = path.popIfMatches(.structField, index: sea.fieldIndex) {
      return .some(sea, newPath)
    }
  case let tea as TupleElementAddrInst:
    if let newPath = path.popIfMatches(.tupleField, index: tea.fieldIndex) {
      return .some(tea, newPath)
    }
  case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
    let ei = instruction as! EnumInst
    if let newPath = path.popIfMatches(.enumCase, index: ei.caseIndex) {
      return .some(ei, newPath)
    }
  // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
  case let ds as DestructureStructInst:
    if let (index, newPath) = path.pop(kind: .structField) {
      return .some(ds.results[index], newPath)
    }
  case let dt as DestructureTupleInst:
    if let (index, newPath) = path.pop(kind: .tupleField) {
      return .some(dt.results[index], newPath)
    }
  // MARK: Non-Address to Non-Address Forwarding Instructions
  case is InitExistentialRefInst, is OpenExistentialRefInst,
       is BeginBorrowInst, is CopyValueInst,
       is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
       is RefToBridgeObjectInst, is BridgeObjectToRefInst:
    return .some(instruction as! SingleValueInstruction, path)
  case let bcm as BeginCOWMutationInst:
    return .some(bcm.bufferResult, path)
  // MARK: Address to Address Forwarding Instructions
  case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
       is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
    return .some(instruction as! SingleValueInstruction, path)
  case let mdi as MarkDependenceInst where operand.index == 0:
    return .some(mdi, path)
  default:
    return .unmatchedInstruction
  }
  return .unmatchedPath
}


func operandDefinition(value: Value, path: SmallProjectionPath) -> ResultPath {
  switch value {
  // MARK: (trivially Non-Address to Non-Address) Constructions
  case let str as StructInst:
    if let (index, newPath) = path.pop(kind: .structField) {
      return .some(str.operands[index].value, newPath)
    }
  case let t as TupleInst:
    if let (index, newPath) = path.pop(kind: .tupleField) {
      return .some(t.operands[index].value, newPath)
    }
  case let e as EnumInst:
    TODO("Asymmetric case from above, also in escape info")
  // MARK: Non-Address to Non-Address Projections
  case let se as StructExtractInst:
    return .some(se.operand, path.push(.structField, index: se.fieldIndex))
  case let ued as UncheckedEnumDataInst:
    return .some(ued.operand, path.push(.enumCase, index: ued.caseIndex))
  // MARK: Non-Address to Address Projections
  case let rta as RefTailAddrInst:
    return .some(rta.operand, path.push(.tailElements))
  case let rea as RefElementAddrInst:
    return .some(rea.operand, path.push(.classField, index: rea.fieldIndex))
  case let pb as ProjectBoxInst:
    return .some(pb.operand, path.push(.classField, index: pb.fieldIndex))
  // MARK: Address to Address Projections
  case let sea as StructElementAddrInst:
    return .some(sea.operand, path.push(.structField, index: sea.fieldIndex))
  case let tea as TupleElementAddrInst:
    return .some(tea.operand, path.push(.tupleField, index: tea.fieldIndex))
  case is InitEnumDataAddrInst, is UncheckedTakeEnumDataAddrInst:
    let ei = value as! EnumInst
    return .some(ei.operand, path.push(.enumCase, index: ei.caseIndex))
  // MARK: (trivially Non-Address to Non-Address) Multiresult Projections
  case let mvr as MultipleValueInstructionResult
    where mvr.instruction is DestructureStructInst:
    let ds = mvr.instruction as! DestructureStructInst
    return .some(ds.operand, path.push(.structField, index: mvr.index))
  case let mvr as MultipleValueInstructionResult
    where mvr.instruction is DestructureTupleInst:
    let dt = mvr.instruction as! DestructureTupleInst
    return .some(dt.operand, path.push(.tupleField, index: mvr.index))
  // MARK: Non-Address to Non-Address Forwarding Instructions
  case is InitExistentialRefInst, is OpenExistentialRefInst,
       is BeginBorrowInst, is CopyValueInst,
       is UpcastInst, is UncheckedRefCastInst, is EndCOWMutationInst,
       is RefToBridgeObjectInst, is BridgeObjectToRefInst:
    return .some((value as! Instruction).operands[0].value, path)
  case let mvr as MultipleValueInstructionResult
    where mvr.instruction is BeginCOWMutationInst:
    let bcm = (mvr.instruction as! BeginCOWMutationInst)
    return .some(bcm.operand, path)
  // MARK: Address to Address Forwarding Instructions
  case is InitExistentialAddrInst, is OpenExistentialAddrInst, is BeginAccessInst,
       is PointerToAddressInst, is AddressToPointerInst, is IndexAddrInst:
    return .some((value as! Instruction).operands[0].value, path)
  case let mdi as MarkDependenceInst:
    return .some((mdi as Instruction).operands[0].value, path)
  default:
    return .unmatchedInstruction
  }
  return .unmatchedPath
}
