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

let escapeInfoDumper2 = FunctionPass(name: "dump-escape-info2", {
  (function: Function, context: PassContext) in
  
  print("Escape information for \(function.name):")
  
  struct VisitFuns : VisitFunctions {
    typealias State = EscapeInfoState
    var results: Set<String> = Set()
    
    mutating
    func reset() {
      results.removeAll(keepingCapacity: true)
    }
    
    mutating
    func visitUse(operand: Operand, path: SmallProjectionPath, state: EscapeInfoState) -> EscapeInfoState {
      print("visitUse \"\(path)\": #\(operand.index) \(operand.instruction)")
      if operand.instruction is ReturnInst {
        results.insert("return[\(path)]")
        return state.with(result: .stopWalk)
      }
      return state.with(result: .continueWalk)
    }
    
    mutating
    func visitDef(def: Value, path: SmallProjectionPath, state: EscapeInfoState) -> EscapeInfoState {
      print("visitDef \"\(path)\": \(def)")
      guard let arg = def as? FunctionArgument else {
        return state.with(result: .continueWalk)
      }
      results.insert("arg\(arg.index)[\(path)]")
      return state.with(result: .continueWalk).with(walkDown: true)
    }
  }
  
  var EIV = EscapeInfoVisitor(calleeAnalysis: context.calleeAnalysis, visitFunctions: VisitFuns())
  
  for block in function.blocks {
    for inst in block.instructions {
      if let allocRef = inst as? AllocRefInst {
        
        EIV.visitFunctions.reset()
        let escapes = EIV.isEscaping(object: allocRef)
        let results = EIV.visitFunctions.results
        
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
