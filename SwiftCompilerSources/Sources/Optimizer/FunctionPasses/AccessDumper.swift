//===--- AccessDumper.swift - Compute effects              ----------------===//
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

let accessDumper = FunctionPass(name: "dump-access", {
  (function: Function, context: PassContext) in
  print("Accesses for \(function.name)")

  var apw = AccessPathWalker()
  var arw = AccessStoragePathWalker()
  for block in function.blocks {
    for instr in block.instructions {
      switch instr {
      case let st as StoreInst:
        printAccessInfo(st.destinationOperand.value, &apw, &arw, context)
      case let load as LoadInst:
        printAccessInfo(load.operand, &apw, &arw, context)
      default:
        break
      }
    }
  }

  print("End accesses for \(function.name)")
})

private func printAccessInfo(_ value: Value, _ apw: inout AccessPathWalker, _ aspw: inout AccessStoragePathWalker,
                             _ ctx: PassContext) {
  print("Value: \(value)")
  let (ap, scope) = apw.getAccessPathWithScope(of: value)
  if let scope = scope {
    switch scope {
    case let .scope(ba):
      print("  Scope: \(ba)")
    case .base(_):
      print("  Scope: base")
    }
  }
  if let ap = ap {
    print("  Base: \(ap.base)")
    print("  Path: \"\(ap.projectionPath)\"")

    for r in aspw.compute(ap) {
      print("    Storage: \(r.storage)")
      print("    Path: \"\(r.path)\"")
    }
  }
}
