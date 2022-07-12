//===--- EffectInference.swift - Compute effects          ----------------===//
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

func theOperand(_ instr: Instruction) -> Value? {
  switch instr {
  case let st as StoreInst:
    return st.destinationOperand.value
  case let load as LoadInst:
    return load.operand
  default:
    return nil
  }
}

func infer(_ function: Function) {
  var apw = AccessPathWalker()
  var arw = AccessRootWalker()
  for block in function.blocks {
    for instr in block.instructions {
      if let op = theOperand(instr) {
        print("Instr: \(instr)")
        let (ap, scope) = apw.pathWithScope(of: op)
        if let scope = scope {
          switch scope {
          case let .scope(scope):
            print("  Scope: \(scope.beginAccess)")
          case .base(_):
            print("  Scope: base")
          }
        }
        if let ap = ap {
          print("  Base: \(ap.base)")
          print("  Path: \(ap.projectionPath)")
          if let roots = arw.compute(ap) {
            for r in roots {
              print("    Root: \(r.root)")
              print("    Path: \(r.path)")
            }
          }
        }
      }
    }
  }
}

struct EffectState {
  var argumentEffects: [SideEffect]
  var globalEffects: SideEffect = SideEffect()
  
  var traps: Bool = false
  var readsRC: Bool = false
  
  init(_ nargs: Int) {
    argumentEffects = []
    argumentEffects.reserveCapacity(nargs)
  }
  
  func update() {
  }
}

let effectInference = FunctionPass(name: "infer-effects", {
  (function: Function, context: PassContext) in


  print("Computing effects for \(function.name)")
  infer(function)
  context.modifyEffects(in: function, {effects in
    effects.argumentEffects.append(
      ArgumentEffect(
        .sideeffect(SideEffect(read: true, write: false)),
        selectedArg: ArgumentEffect.Selection(.argument(0), pathPattern: SmallProjectionPath())
      )
    )
  })
  print("End computing effects for \(function.name)")
})
