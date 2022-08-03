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

let effectInference = FunctionPass(name: "infer-effects", {
  (function: Function, context: PassContext) in
  var effectState = EffectState(function.entryBlock.arguments.endIndex, context.calleeAnalysis)

  for block in function.blocks {
    for inst in block.instructions {
      effectState.update(for: inst)
    }
  }

  context.modifyEffects(in: function, { effects in
    effects.globalEffects = effectState.globalEffects
    for (idx, (effect, path)) in effectState.argumentEffects.enumerated() {
      effects.argumentEffects.append(
        ArgumentEffect(
          .sideeffect(effect),
          selectedArg: ArgumentEffect.Selection(.argument(idx), pathPattern: effect.isPure ? SmallProjectionPath(): path!)
        )
      )
    }
  })
})


private struct EffectState {
  var argumentEffects: [(effect: SideEffect, path: SmallProjectionPath?)]
  var globalEffects: GlobalEffects = GlobalEffects(isValid: true)
  var localEffects: SideEffect = SideEffect()

  var accessPathWalker = AccessPathWalker()
  var accessStorageWalker = AccessStoragePathWalker()

  private let calleeAnalysis: CalleeAnalysis

  init(_ nargs: Int, _ calleeAnalysis: CalleeAnalysis) {
    argumentEffects = Array(repeating: (SideEffect(), nil), count: nargs)
    self.calleeAnalysis = calleeAnalysis
  }

  mutating
  func update(for inst: Instruction) {
    var matched = true
    switch inst {
    case let apply as ApplyInst:
      guard let callees = calleeAnalysis.getCallees(callee: apply.callee) else { return globalEffects.setWorstEffects() }

      for callee in callees {
        // Collect callee `sideeffect`s
        let effects = callee.effects
        let sideeffects = effects.argumentEffects.lazy.compactMap({
          switch $0.kind {
          case let .sideeffect(effect):
            return ($0.selectedArg.argumentIndex, effect)
          default:
            return nil
          }
        })

        // Update global effects
        globalEffects.merge(callee.effects.globalEffects)

        // Update argument effects
        let arguments = apply.argumentOperands
        for (paramIdx, effect) in sideeffects {
          if let argIdx = apply.callerArgIndex(calleeArgIndex: paramIdx) {
            updateEffect(to: arguments[argIdx].value, { $0.merge(effect) })
          } else {
            globalEffects.sideeffect.merge(effect)
          }
        }
      }
    case let fl as FixLifetimeInst:
      return updateEffect(to: fl.operand, { $0.read = true })
    case is AllocStackInst, is DeallocStackInst:
      break
    case let ba as BeginAccessInst:
      if !ba.isStatic {
        globalEffects.traps = true
      }
    case is EndAccessInst, is BeginBorrowInst, is EndBorrowInst:
      break
    case is AllocRefInst, is AllocRefDynamicInst:
      globalEffects.allocates = true
    case is StrongRetainInst, is RetainValueInst:
      // TODO: strong_retain_unowned etc?
      updateEffect(to: (inst as! UnaryInstruction).operand, {
        $0.retain = true
      })
    case is StrongReleaseInst, is ReleaseValueInst:
      updateEffect(to: (inst as! UnaryInstruction).operand, { $0.release = true })
    case let cast as UnconditionalCheckedCastInst:
      updateEffect(to: cast.operand, { $0.read = true })
      globalEffects.traps = true
    case let lb as LoadBorrowInst:
      updateEffect(to: lb.operand, { $0.read = true })
    case let load as LoadInst:
      updateEffect(to: load.operand, {
        $0.read = true
        // TODO: Ownership Qualifier?
      })
    case let store as StoreInst:
      updateEffect(to: store.destinationOperand.value, {
        $0.write = true
        if store.destinationOwnership == .assign {
          $0.release = true
        }
      })
    case is CondFailInst:
      globalEffects.traps = true
    case let pa as PartialApplyInst:
      for (i, arg) in pa.arguments.enumerated() {
        if pa.getArgumentConvention(calleeArgIndex: i).isIndirect {
          updateEffect(to: arg) { $0.read = true }
        }
      }
    case let bi as BuiltinInst:
      switch bi.id {
      case .IsUnique:
        globalEffects.readsRC = true
      case .CondUnreachable:
        globalEffects.traps = true
      default:
        matched = false
      }
    default:
      matched = false
    }

    if !matched {
      globalEffects.sideeffect.read = globalEffects.sideeffect.read || inst.mayReadFromMemory
      globalEffects.sideeffect.write = globalEffects.sideeffect.write || inst.mayWriteToMemory
      if inst.mayHaveSideEffects {
        globalEffects.setWorstEffects()
      }

      if inst.mayTrap {
        globalEffects.traps = true
      }
    }
  }

    private mutating
  func updateEffect(_ origin: Value, _ update: (inout SideEffect) -> (), _ path: SmallProjectionPath! = nil) {
    switch origin {
    case let arg as FunctionArgument:
      update(&argumentEffects[arg.index].effect)
      if let oldPath = argumentEffects[arg.index].path {
        argumentEffects[arg.index].path = oldPath.merge(with: path)
      } else {
        argumentEffects[arg.index].path = path
      }
    case is Allocation:
      update(&localEffects)
    default:
      update(&globalEffects.sideeffect)
    }
  }

  private mutating
  func updateEffect(to value: Value, _ update: (inout SideEffect) -> ()) {
    if value.type.isAddress {
      guard let ap = accessPathWalker.getAccessPath(of: value) else { return globalEffects.setWorstEffects() }
      let ba = ap.base.baseAddress
      if ba is Allocation {
        update(&localEffects)
      } else if let _ = ba as? FunctionArgument {
        updateEffect(ba, update, ap.projectionPath)
      } else if let _ = ap.base.reference {
        let roots = accessStorageWalker.compute(ap)
        for root in roots {
          updateEffect(root.storage, update, root.path)
        }
      } else {
        update(&globalEffects.sideeffect)
      }
    } else {
      let roots = accessStorageWalker.compute(value)
      for root in roots {
        updateEffect(root.storage, update, root.path)
      }
    }
  }
}
