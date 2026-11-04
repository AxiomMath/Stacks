module

public meta import Lean

/-!
# Reading the arguments of a definition off its body

A definition such as `def P := F a₁ … aₙ` is elaborated once, and the proofs inside its body
(instances of `Prop`-valued classes, side conditions) are abstracted into auxiliary lemmas
`P._proof_i`. A second elaboration of the same text `F a₁ … aₙ` in another module produces other
auxiliary lemmas. The two terms are definitionally equal, but the kernel compares them field by
field after unfolding `F`, which for large structures (extension problems, ringed topoi) costs
hundreds of thousands of heartbeats per comparison. Terms read off the body of `P` itself are
syntactically those of `P`, and the kernel compares them by name.

* `unfold_arg% t x`: unfold the head constant of `t` once and return the argument of the
  resulting application bound to the binder named `x`.
* `arg_of% t x`: the argument of the application `t` bound to the binder named `x`.
* `pull_app% t c`: unfold the head constant of `t` once and apply the constant `c` to the
  arguments of the resulting application, binder by binder: a binder of `c` is filled with the
  argument of the same name (an instance binder with an instance argument of the same type; a
  binder without a namesake with the argument at the same position; an instance binder without a
  counterpart is synthesized), as long as one fits. The
  remaining binders of `c` are left to the usual application elaborator. `pull_app_until% t c x`
  stops at the binder of `c` named `x`.
-/

public meta section

open Lean Elab Term Meta

namespace Stacks.DefinitionArguments

/-- The names of the binders of the type of the constant `c`, with macro scopes erased, and
whether each is an instance binder. -/
def binderNames (c : Name) : MetaM (Array (Name × Bool)) := do
  forallTelescope (← getConstInfo c).type fun xs _ =>
    xs.mapM fun y => do
      let d ← y.fvarId!.getDecl
      return (d.userName.eraseMacroScopes, d.binderInfo.isInstImplicit)

/-- Elaborate `t` and unfold its head constant once, beta-reducing the result. -/
def elabUnfold (t : Syntax) : TermElabM Expr := do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some e' ← unfoldDefinition? e | throwError "cannot unfold the head of{indentExpr e}"
  return e'.headBeta

/-- The argument of the application `e` of a constant bound to the binder named `x`. -/
def argOf (e : Expr) (x : Name) : MetaM Expr := do
  let .const c _ := e.getAppFn | throwError "the head of{indentExpr e}\nis not a constant"
  let names ← binderNames c
  let some i := names.findIdx? (·.1 == x) | throwError "{c} has no binder named {x}"
  let some a := e.getAppArgs[i]? | throwError "{c} is applied to too few arguments"
  return a

/-- `unfold_arg% t x`: unfold the head constant of `t` once; the result is an application of a
constant, and this is its argument bound to the binder named `x`. -/
elab "unfold_arg% " t:term:max x:ident : term => do
  argOf (← elabUnfold t) x.getId

/-- `arg_of% t x`: `t` is an application of a constant, and this is its argument bound to the
binder named `x`. -/
elab "arg_of% " t:term:max x:ident : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  argOf (← instantiateMVars e) x.getId

/-- The elaboration of `pull_app% t c` (`stopName = none`) and `pull_app_until% t c x`: unfold
the head constant of `t` once, to an application of a constant `c₀`, and apply `c` to its
arguments. Each leading binder of `c` is filled with the argument of `c₀` of the same name (an
instance binder with an instance argument of `c₀` of the same type, a binder without a namesake
with the argument at the same position, an instance binder without a counterpart by instance
synthesis), as long as one fits. With `stopName = some x`, it stops at the binder named `x`. -/
def pullApp (t : Syntax) (c : Ident) (stopName : Option Name) : TermElabM Expr := do
  let e' ← elabUnfold t
  let .const src _ := e'.getAppFn | throwError "the head of{indentExpr e'}\nis not a constant"
  let srcArgs := e'.getAppArgs
  let srcBinders ← binderNames src
  let c ← realizeGlobalConstNoOverload c
  let cinfo ← getConstInfo c
  let us ← mkFreshLevelMVarsFor cinfo
  let mut fn := Expr.const c us
  let mut ty := cinfo.type.instantiateLevelParams cinfo.levelParams us
  let mut used : Array Nat := #[]
  for _ in [0:srcArgs.size + 64] do
    let .forallE n d b bi := ty | break
    if let some x := stopName then
      if n.eraseMacroScopes == x then break
    let mut found : Option (Nat × Expr) := none
    for h : i in [0:srcArgs.size] do
      if found.isNone && !used.contains i && i < srcBinders.size then
        let (sn, sinst) := srcBinders[i]!
        if (if bi.isInstImplicit then sinst else sn == n.eraseMacroScopes) then
          if ← isDefEq (← inferType srcArgs[i]) d then found := some (i, srcArgs[i])
    if found.isNone && !bi.isInstImplicit then
      let i := used.size
      if h : i < srcArgs.size then
        if !used.contains i then
          if ← isDefEq (← inferType srcArgs[i]) d then found := some (i, srcArgs[i])
    match found with
    | some (i, a) =>
      used := used.push i
      fn := mkApp fn a
      ty := b.instantiate1 a
    | none =>
      -- an instance binder of `c` without a counterpart in `c₀` is synthesized
      if bi.isInstImplicit then
        let some a ← (do return some (← synthInstance (← instantiateMVars d))) <|>
          (return none) | break
        fn := mkApp fn a
        ty := b.instantiate1 a
      else break
  instantiateMVars fn

/-- `pull_app% t c`: unfold the head constant of `t` once, to an application of a constant
`c₀`, and apply `c` to its arguments, binder by binder (`Stacks.DefinitionArguments.pullApp`). -/
elab "pull_app% " t:term:max c:ident : term => pullApp t c none

/-- `pull_app_until% t c x`: `pull_app% t c`, stopping at the binder of `c` named `x`. -/
elab "pull_app_until% " t:term:max c:ident x:ident : term => pullApp t c (some x.getId)

end Stacks.DefinitionArguments
