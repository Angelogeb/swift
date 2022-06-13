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

class EIWVisitor : EscapeInfoWalkerVisitor {
  var results: Set<String> =  Set()
  
  func visitUse(operand: Operand, path: Path, state: State) -> UseVisitResult {
    print("visitUse \"\(path)\": #\(operand.index) \(operand.instruction)")
    if operand.instruction is ReturnInst {
      results.insert("return[\(path)]")
      return .ignore
    }
    return .continueWalk
  }
  
  func visitDef(def: Value, path: Path, state: State) -> DefVisitResult {
    print("visitDef \"\(path)\": \(def)")
    guard let arg = def as? FunctionArgument else {
      return .continueWalkUp
    }
    results.insert("arg\(arg.index)[\(path)]")
    return .walkDown
  }
}

let escapeInfoDumper2 = FunctionPass(name: "dump-escape-info2", {
  (function: Function, context: PassContext) in
  
  print("Escape information for \(function.name):")
  
  let visitor = EIWVisitor()
  var walker = EscapeInfoWalker(calleeAnalysis: context.calleeAnalysis)
  
  for block in function.blocks {
    for inst in block.instructions {
      if let allocRef = inst as? AllocRefInst {
        
        visitor.results.removeAll(keepingCapacity: true)
        let escapes = walker.isEscaping(object: allocRef, visitor: visitor)
        let results = visitor.results
        
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
