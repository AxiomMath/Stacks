module

public meta import Lean

/-!
# Applying a lemma with its implicit arguments read off by matching, checked by the kernel

A pasting lemma proved in an arbitrary category, such as `f ≫ g = h` from a few commuting
squares, is applied to hypotheses produced by different library lemmas.  These hypotheses
mention the same morphisms, but the implicit objects and categories inside them can be spelled
differently: `G.map (F.map x)` with the source category of `G` written as the target category of
`F` in one hypothesis and as the source category of `G` in another, or the same scheme reached
through two definitionally equal sites.  The elaborator then has to unify these spellings when it
instantiates the implicit arguments of the lemma, and in large categories of sheaves of modules
this can exhaust its heartbeats even though the kernel accepts the same identifications at once.

* `kernel_apply f h₁ … hₙ` closes the main goal by `f h₁ … hₙ` without unifying anything: every
  implicit argument of `f` is read off the types of the explicit arguments `hᵢ` (and then of the
  goal) by structural matching, the first occurrence of an argument fixing it.  An argument that
  is an equation spelled differently from the instantiated hypothesis of `f` is bridged to it by
  congruence.
* `kernel_have h := f h₁ … hₙ` adds the same term as a hypothesis, at the type it has in the
  spelling of the `hᵢ`.
* `kernel_congr` closes `a = b` or `HEq a b` between two spellings of the same term by
  congruence through compositions, images under functors, components, halves of isomorphisms,
  kernels and cokernels, unfolding composites of isomorphisms on the way.

The kernel, unlike the elaborator, accepts the identification of two spellings cheaply when it
can compare them argument by argument; it does not do so at projections such as
`CategoryTheory.NatTrans.app`, which it unfolds instead, and the congruence proofs built here
hand it the arguments one at a time.  All three tactics assign their proof terms unchecked; the
kernel checks them when the declaration is added, so a wrong application is an error at that
point and never an unsound result.
-/

@[expose] public section

/-- Two terms are equal if they are heterogeneously equal to the two sides of an equation
between terms of another type. -/
theorem Stacks.KernelApply.eq_of_heq_of_eq_of_heq.{w} {α β : Sort w} {a b : α} {c d : β}
    (h₁ : HEq a c) (h : c = d) (h₂ : HEq d b) : a = b :=
  eq_of_heq ((h₁.trans (heq_of_eq h)).trans h₂)

meta section

open Lean Meta Elab Tactic

namespace Stacks.KernelApply

/-- Assign the metavariables of the pattern `p` by structural matching against `e`: an unassigned
metavariable is assigned the corresponding subterm of `e`, universe metavariables are assigned
by matching the levels of constants and sorts, and the two terms are traversed in parallel where
they are applications of the same constant (or local) to the same number of arguments.
Nothing is checked: where the shapes disagree the subterm is skipped.  The depth of the traversal
is bounded by `fuel`. -/
def matchAssign : Nat → Expr → Expr → MetaM Unit
  | 0, _, _ => pure ()
  | fuel + 1, p, e => do
    let e := e.consumeMData
    match p.consumeMData with
    | .mvar m =>
      unless ← m.isAssigned do
        unless ← m.isDelayedAssigned do
          m.assign e
    | .const _ ls =>
      if let .const _ ls' := e then
        if ls.length == ls'.length then
          for (a, b) in ls.zip ls' do
            discard <| isLevelDefEq a b
    | .sort l =>
      if let .sort l' := e then discard <| isLevelDefEq l l'
    | p@(.app ..) =>
      let fp := p.getAppFn
      let fe := e.getAppFn
      let sameHead := match fp, fe with
        | .const n _, .const n' _ => n == n'
        | .fvar x, .fvar y => x == y
        | _, _ => false
      if e.isApp && p.getAppNumArgs == e.getAppNumArgs && sameHead then
        matchAssign fuel fp fe
        for i in [0:p.getAppNumArgs] do
          matchAssign fuel (p.getArg! i) (e.getArg! i)
    | .forallE _ t b _ =>
      if let .forallE _ t' b' _ := e then
        matchAssign fuel t t'
        if !b.hasLooseBVars && !b'.hasLooseBVars then matchAssign fuel b b'
    | .lam _ t _ _ =>
      if let .lam _ t' _ _ := e then matchAssign fuel t t'
    | .proj _ _ x =>
      if let .proj _ _ x' := e then matchAssign fuel x x'
    | _ => pure ()

end Stacks.KernelApply

namespace Stacks.KernelApply

/-- The heads through which `Stacks.KernelApply.congrHEq` decomposes: composition, images under
functors, components of natural transformations, the two halves of an isomorphism, inverses, and
kernels and cokernels, and images of objects.  An image of an object is decomposed only when the
two functors have the same head (`Stacks.KernelApply.decomposes`): `(F ⋙ G).obj X` and
`G.obj (F.obj X)` are applications of the same constant whose arguments do not correspond. -/
def congrHeads : List Name :=
  [`CategoryTheory.Functor.map, `CategoryTheory.NatTrans.app,
    `CategoryTheory.CategoryStruct.comp, `CategoryTheory.Iso.hom, `CategoryTheory.Iso.inv,
    `CategoryTheory.inv, `CategoryTheory.Limits.kernelSubobject,
    `CategoryTheory.Limits.cokernel.π, `CategoryTheory.Limits.cokernel,
    `CategoryTheory.Subobject.arrow, `CategoryTheory.Functor.obj]

/-- Whether `Stacks.KernelApply.congrHEq` decomposes the two applications `a` and `b` of the same
constant: the constant is one of `Stacks.KernelApply.congrHeads`, and for an image of an object
the two functors are applications of the same constant, so that the arguments correspond. -/
def decomposes (a b : Expr) : Bool :=
  let fa := a.getAppFn
  let fb := b.getAppFn
  let n := a.getAppNumArgs
  n > 0 && fa.isConst && fb.isConst && fa.constName! == fb.constName! &&
    congrHeads.contains fa.constName! && n == b.getAppNumArgs &&
    fa.constLevels! == fb.constLevels! &&
    (fa.constName! != `CategoryTheory.Functor.obj ||
      (n == 6 && (a.getArg! 4).getAppFn.constName? == (b.getArg! 4).getAppFn.constName? &&
        (a.getArg! 4).getAppFn.constName?.isSome))

/-- One step of unfolding of the half `Iso.hom e` of an isomorphism built by `Iso.trans`,
`Functor.mapIso`, `Iso.app` or `Iso.symm` into a composite, an image under a functor, a component
or an inverse; when `e` is the application of another definition, that definition is unfolded
first.  Returns `none` when there is nothing to unfold.  The result is definitionally equal to
the input by the unfolding of a structure-valued definition and a projection. -/
def isoHomStep? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity `CategoryTheory.Iso.hom 5 do return none
  let i := e.appArg!
  let fn := i.getAppFn
  let args := i.getAppArgs
  let some n := fn.constName? | return none
  if n == `CategoryTheory.Iso.trans && args.size ≥ 2 then
    return some (← mkAppM `CategoryTheory.CategoryStruct.comp
      #[← mkAppM `CategoryTheory.Iso.hom #[args[args.size - 2]!],
        ← mkAppM `CategoryTheory.Iso.hom #[args[args.size - 1]!]])
  -- `Functor.mapIso F i`: `F` is the fifth of its eight arguments and `i` the last.
  if n == `CategoryTheory.Functor.mapIso && args.size == 8 then
    return some (← mkAppM `CategoryTheory.Functor.map
      #[args[4]!, ← mkAppM `CategoryTheory.Iso.hom #[args[7]!]])
  if n == `CategoryTheory.Iso.app && args.size ≥ 2 then
    return some (← mkAppM `CategoryTheory.NatTrans.app
      #[← mkAppM `CategoryTheory.Iso.hom #[args[args.size - 2]!], args[args.size - 1]!])
  if n == `CategoryTheory.Iso.symm && args.size ≥ 1 then
    return some (← mkAppM `CategoryTheory.Iso.inv #[args[args.size - 1]!])
  if let some i' ← unfoldDefinition? i then
    return some (mkAppN e.getAppFn (e.getAppArgs.set! 4 i'))
  return none

/-- `HEq.refl a`, at the type of `a`. -/
def heqReflAt (a : Expr) : MetaM Expr := do
  let ty ← inferType a
  return mkApp2 (mkConst ``HEq.refl [← getLevel ty]) ty a

/-- A proof of `HEq a b` for two terms that are the same up to the spelling of their implicit
arguments and up to proofs: where both are applications of the same constant to the same number
of arguments, one of `Stacks.KernelApply.congrHeads`, it is built by the congruence lemma of
`Lean.Meta.mkHCongrWithArity` from proofs for
the arguments, and every other comparison is closed by `HEq.refl` (or proof irrelevance) and left
to the kernel.  The depth of the decomposition is bounded by `fuel`. -/
def congrHEq : Nat → Expr → Expr → MetaM Expr
  | 0, a, _ => heqReflAt a
  | fuel + 1, a, b => do
    if a == b then
      return ← heqReflAt a
    if ← isProof a then
      return mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b
    let fa := a.getAppFn
    let fb := b.getAppFn
    let n := a.getAppNumArgs
    if decomposes a b then
      let thm ← mkHCongrWithArity fa n
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let mut pf := thm.proof
      for i in [0:n] do
        match thm.argKinds[i]! with
        | .eq =>
          let ty ← inferType as[i]!
          let h ← congrHEq fuel as[i]! bs[i]!
          pf := mkApp3 pf as[i]! bs[i]!
            (mkApp4 (mkConst ``eq_of_heq [← getLevel ty]) ty as[i]! bs[i]! h)
        | .heq => pf := mkApp3 pf as[i]! bs[i]! (← congrHEq fuel as[i]! bs[i]!)
        | _ => pf := mkApp pf as[i]!
      return pf
    if fa != fb then
      if let some a' ← isoHomStep? a then
        return ← congrHEq fuel a' b
      if let some b' ← isoHomStep? b then
        return ← congrHEq fuel a b'
    heqReflAt a

end Stacks.KernelApply

namespace Stacks.KernelApply

/-- The constant `f` applied to the elaborated explicit arguments `args`, with every implicit
argument read off by `Stacks.KernelApply.matchAssign` from the types of the explicit arguments and
then from `target?`, together with the type of the application. -/
def buildApp (f : Ident) (args : Array Term) (target? : Option Expr) :
    TacticM (Expr × Expr) := do
  let c ← realizeGlobalConstNoOverloadWithInfo f
  let fe ← mkConstWithFreshMVarLevels c
  let (mvs, bis, concl) ← forallMetaTelescope (← inferType fe)
  let mut rest := args.toList
  let mut given : Array (Nat × Expr × Expr) := #[]
  for i in [0:mvs.size] do
    if bis[i]! == .default then
      match rest with
      | [] => throwError "kernel_apply: too few explicit arguments"
      | a :: as =>
        rest := as
        let ae ← Term.withSynthesize <| Term.elabTerm a none
        let ae ← instantiateMVars ae
        let aty ← instantiateMVars (← inferType ae)
        matchAssign 4096 (← inferType mvs[i]!) aty
        let m := mvs[i]!.mvarId!
        if aty.consumeMData.isAppOfArity ``Eq 3 then
          given := given.push (i, ae, aty)
        else
          unless ← m.isAssigned do m.assign ae
  unless rest.isEmpty do throwError "kernel_apply: too many explicit arguments"
  if let some t := target? then matchAssign 4096 concl t
  -- An explicit argument that is an equation spelled differently from the instantiated binder
  -- type is bridged to it by congruence.
  for (i, ae, aty) in given do
    let m := mvs[i]!.mvarId!
    unless ← m.isAssigned do
      let bty ← instantiateMVars (← m.getType)
      let aty' := aty.consumeMData
      let bty' := bty.consumeMData
      if !bty.hasExprMVar && bty' != aty' && bty'.isAppOfArity ``Eq 3 then
        let ba := bty'.getAppArgs
        let aa := aty'.getAppArgs
        let h₁ ← congrHEq 1024 ba[1]! aa[1]!
        let h₂ ← congrHEq 1024 aa[2]! ba[2]!
        m.assign (mkAppN (mkConst ``Stacks.KernelApply.eq_of_heq_of_eq_of_heq
          [← getLevel ba[0]!]) #[ba[0]!, aa[0]!, ba[1]!, ba[2]!, aa[1]!, aa[2]!, h₁, ae, h₂])
      else
        m.assign ae
  for i in [0:mvs.size] do
    let m := mvs[i]!.mvarId!
    unless ← m.isAssigned do
      if bis[i]! == .instImplicit then
        m.assign (← synthInstance (← instantiateMVars (← m.getType)))
  let val ← instantiateMVars (mkAppN fe mvs)
  let ty ← instantiateMVars concl
  if val.hasExprMVar || val.hasLevelMVar || ty.hasExprMVar then
    throwError "kernel_apply: could not read off every argument of {c}"
  return (val, ty)

end Stacks.KernelApply

open Stacks.KernelApply in
/-- `kernel_apply f h₁ … hₙ` closes the main goal by the constant `f` applied to the explicit
arguments `h₁ … hₙ`, reading every implicit argument of `f` off the types of the `hᵢ` and of the
goal by structural matching, and leaving all definitional checks to the kernel.  See
`Stacks.KernelApply.matchAssign`. -/
elab "kernel_apply " f:ident args:(ppSpace colGt term:max)* : tactic => withMainContext do
  let (val, _) ← buildApp f args (some (← instantiateMVars (← getMainTarget)))
  (← getMainGoal).assign val
  replaceMainGoal []

open Stacks.KernelApply in
/-- `kernel_have h := f h₁ … hₙ` adds the hypothesis `h` proved by the constant `f` applied to
the explicit arguments `h₁ … hₙ`, every implicit argument of `f` read off the types of the `hᵢ`
by structural matching; its type is the conclusion of `f` so instantiated, in the spelling of
the `hᵢ`, and all definitional checks are left to the kernel. -/
elab "kernel_have " h:ident " := " f:ident args:(ppSpace colGt term:max)* : tactic =>
  withMainContext do
    let (val, ty) ← buildApp f args none
    let g ← getMainGoal
    let g' ← g.assert h.getId ty val
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']



open Stacks.KernelApply in
/-- Close a goal `HEq a b` or `a = b` in which `a` and `b` are the same term up to the spelling
of their implicit arguments and up to proofs, by congruence (`Stacks.KernelApply.congrHEq`); the
remaining definitional checks, between differently spelled arguments, are left to the kernel. -/
elab "kernel_congr" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``HEq 4 then
    let args := t.getAppArgs
    g.assign (← congrHEq 1024 args[1]! args[3]!)
  else if t.isAppOfArity ``Eq 3 then
    let args := t.getAppArgs
    let h ← congrHEq 1024 args[1]! args[2]!
    g.assign (mkApp4 (mkConst ``eq_of_heq t.getAppFn.constLevels!) args[0]! args[1]! args[2]! h)
  else
    throwError "kernel_congr: the goal is not an equality"
  replaceMainGoal []

end
