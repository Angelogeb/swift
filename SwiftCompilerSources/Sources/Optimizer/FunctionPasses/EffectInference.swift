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
          let roots = arw.compute(ap)
          for r in roots {
            print("    Root: \(r.root)")
            print("    Path: \(r.path)")
          }
        }
      }
    }
  }
}

struct EffectState {
  var argumentEffects: [SideEffect]
  var globalEffects: SideEffect = SideEffect()
  var localEffects: SideEffect = SideEffect()
  
  var traps: Bool = false
  var readsRC: Bool = false
  
  var accessPathWalker = AccessPathWalker()
  var accessRootWalker = AccessRootWalker()
  
  init(_ nargs: Int) {
    argumentEffects = Array(repeating: SideEffect(), count: nargs)
  }
  
  private
  func isLocallyAllocated(_ value: Value) -> Bool {
    switch value {
    case is AllocStackInst, is AllocRefInst, is AllocRefDynamicInst, is AllocBoxInst:
      return true
    default:
      return false
    }
  }
  
  private mutating
  func updateEffect(_ origin: Value, _ update: (inout SideEffect) -> ()) {
    switch origin {
    case let arg as FunctionArgument:
      update(&argumentEffects[arg.index])
    case _ where isLocallyAllocated(origin):
      update(&localEffects)
    default:
      update(&globalEffects)
    }
  }
  
  private mutating
  func updateEffect(to value: Value, _ update: (inout SideEffect) -> ()) {
    if value.type.isAddress {
      guard let ap = accessPathWalker.compute(value) else { return globalEffects.setWorstEffects() }
      let ba = ap.base.baseAddress
      if isLocallyAllocated(ba) {
        updateEffect(ba, update)
      } else if let _ = ba as? FunctionArgument {
        updateEffect(ba, update)
      } else if let _ = ap.base.reference {
        let roots = accessRootWalker.compute(ap)
        for root in roots {
          updateEffect(root.root, update)
        }
      } else {
        update(&globalEffects)
      }
    } else {
      let roots = accessRootWalker.compute(value)
      for root in roots {
        updateEffect(root.root, update)
      }
    }
  }
  
  mutating
  func update(for inst: Instruction) {
    switch inst {
    case is ApplyInst:
      let appsite = inst as! FullApplySite
      let effects = appsite.function.effects
      let sideeffects: [(Int, SideEffect)] = effects.argumentEffects.compactMap({
        switch $0.kind {
        case let .sideeffect(eff):
          return ($0.selectedArg.argumentIndex, eff)
        default:
          return nil
        }
      })
      let arguments: [Value] = appsite.arguments.map({ $0 })
      for (paramIdx, eff) in sideeffects {
        let argIdx = appsite.callerArgIndex(calleeArgIndex: paramIdx)!
        updateEffect(to: arguments[argIdx], { $0.merge(eff) })
      }
    case let fl as FixLifetimeInst:
      updateEffect(to: fl.operand, { $0.read = true })
    case is AllocStackInst, is DeallocStackInst:
      break
    case is StrongRetainInst, is RetainValueInst:
      // TODO: strong_retain_unowned etc?
      updateEffect(to: (inst as! UnaryInstruction).operand, { $0.retain = true })
    case is StrongReleaseInst, is ReleaseValueInst:
      updateEffect(to: (inst as! UnaryInstruction).operand, { $0.release = true })
    case let cast as UnconditionalCheckedCastInst:
      updateEffect(to: cast.operand, { $0.read = true })
      traps = true
    case let lb as LoadBorrowInst:
      updateEffect(to: lb.operand, { $0.read = true })
    case let load as LoadInst:
      updateEffect(to: load, {
        $0.read = true
        // Ownership Qualifier?
      })
    case let store as StoreInst:
      updateEffect(to: store.destinationOperand.value, {
        $0.write = true
        if store.destinationOwnership == .assign {
          $0.release = true
        }
      })
    case is CondFailInst:
      traps = true
    case let pa as PartialApplyInst:
      fatalError("TODO")
    case let bi as BuiltinInst:
      fatalError("TODO")
    default:
      break
    }
    
    globalEffects.read = inst.mayReadFromMemory
    globalEffects.write = inst.mayWriteToMemory
    if inst.mayHaveSideEffects {
      globalEffects.setWorstEffects()
    }
    
    if inst.mayTrap {
      traps = true
    }
  }
}

let effectInference = FunctionPass(name: "infer-effects", {
  (function: Function, context: PassContext) in
  print("Computing effects for \(function.name)")
  
  infer(function)
  
  var effectState = EffectState(function.entryBlock.arguments.endIndex)
  
  for block in function.blocks {
    for inst in block.instructions {
      effectState.update(for: inst)
    }
  }
  
  context.modifyEffects(in: function, { effects in
    for (idx, effect) in effectState.argumentEffects.enumerated() {
      effects.argumentEffects.append(
        ArgumentEffect(
          .sideeffect(effect),
          selectedArg: ArgumentEffect.Selection(.argument(idx), pathPattern: SmallProjectionPath(.anything))
        )
      )
    }
  })
  
  print("End computing effects for \(function.name)")
})
