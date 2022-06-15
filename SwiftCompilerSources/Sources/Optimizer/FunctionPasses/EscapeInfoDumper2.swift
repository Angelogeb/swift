//===--- WalkDumper.swift - Dumps walkup/down info ------------------------===//
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

struct EIWVisitor : EscapeInfoWalkerVisitor {
  var results: Set<String> =  Set()
  
  mutating func visitUse(operand: Operand, path: Path, state: State) -> UseVisitResult {
    if operand.instruction is ReturnInst {
      results.insert("return[\(path)]")
      return .ignore
    }
    return .continueWalk
  }
  
  mutating func visitDef(def: Value, path: Path, state: State) -> DefVisitResult {
    guard let arg = def as? FunctionArgument else {
      return .continueWalkUp
    }
    results.insert("arg\(arg.index)[\(path)]")
    return .walkDown
  }
}

/// Dumps the results of escape analysis.
///
/// Dumps the EscapeInfo query results for all `alloc_stack` instructions in a function.
///
/// This pass is used for testing EscapeInfo.
let escapeInfoDumper2 = FunctionPass(name: "dump-escape-info2", {
  (function: Function, context: PassContext) in
  
  print("Escape information for \(function.name):")
  
  var walker = EscapeInfoWalker(calleeAnalysis: context.calleeAnalysis, visitor: EIWVisitor())
  
  for block in function.blocks {
    for inst in block.instructions {
      if let allocRef = inst as? AllocRefInst {
        
        walker.visitor.results.removeAll(keepingCapacity: true)
        let escapes = walker.isEscaping(object: allocRef)
        let results = walker.visitor.results
        
        let res: String
        if escapes {
          res = "global"
        } else if results.isEmpty {
          res = " -    "
        } else {
          res = Array(results).sorted().joined(separator: ",")
        }
        print("\(res): \(allocRef)")
      }
    }
  }
  print("End function \(function.name)\n")
})


/// Dumps the results of address-related escape analysis.
///
/// Dumps the EscapeInfo query results for addresses escaping to function calls.
/// The `fix_lifetime` instruction is used as marker for addresses and values to query.
///
/// This pass is used for testing EscapeInfo.
let addressEscapeInfoDumper2 = FunctionPass(name: "dump-addr-escape-info2", {
  (function: Function, context: PassContext) in

  print("Address escape information for \(function.name):")

  var valuesToCheck = [Value]()
  var applies = [Instruction]()
  
  for block in function.blocks {
    for inst in block.instructions {
      switch inst {
        case let fli as FixLifetimeInst:
          valuesToCheck.append(fli.operand)
        case is FullApplySite:
          applies.append(inst)
        default:
          break
      }
    }
  }
  
  struct Visitor : EscapeInfoWalkerVisitor {
    let apply: Instruction
    mutating func visitUse(operand: Operand, path: Path, state: State) -> UseVisitResult {
      let user = operand.instruction
      if user == apply {
        return .abort
      }
      if user is ReturnInst {
        // Anything which is returned cannot escape to an instruction inside the function.
        return .ignore
      }
      return .continueWalk
    }
  }

  // test `isEscaping(addressesOf:)`
  for value in valuesToCheck {
    print("value:\(value)")
    for apply in applies {
      let path = AliasAnalysis.getPtrOrAddressPath(for: value)
      
      var escapeInfo = EscapeInfoWalker(calleeAnalysis: context.calleeAnalysis, visitor: Visitor(apply: apply))
      let escaping = escapeInfo.isEscaping(addressesOf: value, path: path)
      print("  \(escaping ? "==>" : "-  ") \(apply)")
    }
  }
  
  var EAA = EscapeAliasAnalysis(calleeAnalysis: context.calleeAnalysis)
  // test `canReferenceSameField` for each pair of `fix_lifetime`.
  if !valuesToCheck.isEmpty {
    for lhsIdx in 0..<(valuesToCheck.count - 1) {
      for rhsIdx in (lhsIdx + 1) ..< valuesToCheck.count {
        print("pair \(lhsIdx) - \(rhsIdx)")
        let lhs = valuesToCheck[lhsIdx]
        let rhs = valuesToCheck[rhsIdx]
        print(lhs)
        print(rhs)
        if EAA.canReferenceSameField(
            lhs, path: AliasAnalysis.getPtrOrAddressPath(for: lhs),
            rhs, path: AliasAnalysis.getPtrOrAddressPath(for: rhs)) {
          print("may alias")
        } else {
          print("no alias")
        }
      }
    }
  }
  
  print("End function \(function.name)\n")
})
