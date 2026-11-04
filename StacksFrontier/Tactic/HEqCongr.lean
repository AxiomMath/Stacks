module

public meta import Lean

/-!
# Heterogeneous equality of morphisms by congruence, checked by the kernel

Two morphisms of a category can be the same term up to the *spelling* of the objects and
categories they mention: `(F ⋙ G).obj X` against `G.obj (F.obj X)`, `(𝟭 C).obj X` against `X`,
or two proofs of the same proposition inside an index.  Such morphisms are heterogeneously equal,
and `HEq.refl` proves it, but asking the elaborator to check that by unification can be
prohibitively expensive in large categories of sheaves of modules: the unifier compares the two
terms by unfolding the definitions they are built from rather than their arguments.

This file provides two tactics that build such proofs by congruence, so that the only
definitional checks left are between objects, categories and functors, and leaves those checks to
the kernel.

* `heq_congr` closes a goal `HEq a b` where `a` and `b` are the same morphism up to spelling: it
  decomposes both sides through composition, images under functors, components of natural
  transformations and the two halves of an isomorphism, using the congruence lemmas of
  `Lean.Meta.mkHCongrWithArity`, and closes every remaining comparison by `HEq.refl`.
* `heq_congr_full` does the same through every common head, comparing proof arguments (such as
  instances spelled in two ways) by proof irrelevance, with a cache on shared subterms.
* `heq_split_map_comp` rewrites a goal `HEq (G.map (f ≫ g)) b` into
  `HEq (G.map f ≫ G.map g) b` by `CategoryTheory.Functor.map_comp`, reading the arguments off the
  goal.

Both tactics assign their proof term without asking the elaborator to unify it with the goal;
the kernel checks it when the declaration is added, so a wrong application is an error at that
point and never an unsound result.
-/

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace Stacks.HEqCongr

/-- The heads through which `heqByCongr` decomposes a morphism. -/
def structuralHeads : List Name :=
  [`CategoryTheory.Functor.map, `CategoryTheory.NatTrans.app,
    `CategoryTheory.CategoryStruct.comp, `CategoryTheory.Iso.hom, `CategoryTheory.Iso.inv]

/-- `HEq.refl a`, at the type of `a`. -/
def mkHEqReflAt (a : Expr) : MetaM Expr := do
  let ty ← inferType a
  return mkApp2 (mkConst ``HEq.refl [← getLevel ty]) ty a

/-- A proof of `HEq a b` for two morphisms `a` and `b` that are the same up to proofs and up to
the spelling of the objects and categories they mention, built by congruence through the heads
`structuralHeads` to depth at most `fuel`; every other comparison is closed by `HEq.refl` and
left to the kernel. -/
def heqByCongrAux : Nat → Expr → Expr → MetaM Expr
  | 0, a, _ => mkHEqReflAt a
  | fuel + 1, a, b => do
    if a == b then
      return ← mkHEqReflAt a
    if ← isProof a then
      return mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b
    let fa := a.getAppFn
    let fb := b.getAppFn
    let n := a.getAppNumArgs
    if fa.isConst && fb.isConst && fa.constName! == fb.constName! && n == b.getAppNumArgs &&
        structuralHeads.contains fa.constName! && fa.constLevels! == fb.constLevels! then
      let thm ← mkHCongrWithArity fa n
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let mut pf := thm.proof
      for i in [0:n] do
        match thm.argKinds[i]! with
        | .eq =>
          let ty ← inferType as[i]!
          let h ← heqByCongrAux fuel as[i]! bs[i]!
          pf := mkApp3 pf as[i]! bs[i]!
            (mkApp4 (mkConst ``eq_of_heq [← getLevel ty]) ty as[i]! bs[i]! h)
        | .heq => pf := mkApp3 pf as[i]! bs[i]! (← heqByCongrAux fuel as[i]! bs[i]!)
        | _ => pf := mkApp pf as[i]!
      return pf
    mkHEqReflAt a

/-- `heqByCongrAux` with a depth bound far beyond the nesting of the morphisms it is used on. -/
def heqByCongr (a b : Expr) : MetaM Expr :=
  heqByCongrAux 256 a b

/-- A proof of `HEq a b` built by congruence through every application whose two sides have the
same head and the same number of arguments, with a cache on pairs of subterms. Arguments that are
proofs are compared by proof irrelevance (`proof_irrel_heq`), so instance arguments spelled
differently cost nothing. Below a head that is not in `structuralHeads`, the congruence proof is
used only when every argument was matched exactly; otherwise the whole application is left to the
kernel by `HEq.refl`. The second component records whether no comparison was left to the kernel. -/
def heqFullAux (cache : IO.Ref (Std.HashMap (Expr × Expr) (Expr × Bool)))
    (ccache : IO.Ref (Std.HashMap (Expr × Nat) CongrTheorem)) :
    Nat → Expr → Expr → MetaM (Expr × Bool)
  | 0, a, _ => return (← mkHEqReflAt a, false)
  | fuel + 1, a, b => do
    if a == b then
      return (← mkHEqReflAt a, true)
    if let some r := (← cache.get)[(a, b)]? then
      return r
    let r ← (do
      let fa := a.getAppFn
      let fb := b.getAppFn
      let n := a.getAppNumArgs
      let sameHead := (fa.isConst && fb.isConst && fa.constName! == fb.constName! &&
          fa.constLevels! == fb.constLevels!) || (fa.isFVar && fa == fb)
      if sameHead && n > 0 && n == b.getAppNumArgs then
        try
          let structural := fa.isConst && structuralHeads.contains fa.constName!
          let thm ← match (← ccache.get)[(fa, n)]? with
            | some t => pure t
            | none => do
              let t ← mkHCongrWithArity fa n
              ccache.modify (·.insert (fa, n) t)
              pure t
          let info ← getFunInfoNArgs fa n
          let as := a.getAppArgs
          let bs := b.getAppArgs
          let mut pf := thm.proof
          let mut exact := true
          for i in [0:n] do
            let isP := i < info.paramInfo.size && info.paramInfo[i]!.isProp
            match thm.argKinds[i]! with
            | .eq =>
              let ty ← inferType as[i]!
              let (h, e) ← if as[i]! == bs[i]! then pure (← mkHEqReflAt as[i]!, true)
                else if isP then pure (mkApp4 (mkConst ``proof_irrel_heq) ty
                  (← inferType bs[i]!) as[i]! bs[i]!, true)
                else heqFullAux cache ccache fuel as[i]! bs[i]!
              exact := exact && e
              pf := mkApp3 pf as[i]! bs[i]!
                (mkApp4 (mkConst ``eq_of_heq [← getLevel ty]) ty as[i]! bs[i]! h)
            | .heq =>
              let (h, e) ← if as[i]! == bs[i]! then pure (← mkHEqReflAt as[i]!, true)
                else if isP then pure (mkApp4 (mkConst ``proof_irrel_heq) (← inferType as[i]!)
                  (← inferType bs[i]!) as[i]! bs[i]!, true)
                else heqFullAux cache ccache fuel as[i]! bs[i]!
              exact := exact && e
              pf := mkApp3 pf as[i]! bs[i]! h
            | _ =>
              unless as[i]! == bs[i]! do throwError "fixed argument differs"
              pf := mkApp pf as[i]!
          if exact || structural then
            return (pf, exact)
          else
            return (← mkHEqReflAt a, false)
        catch _ => return (← mkHEqReflAt a, false)
      else
        return (← mkHEqReflAt a, false) : MetaM (Expr × Bool))
    cache.modify (·.insert (a, b) r)
    return r

/-- The four arguments of a goal `@HEq α a β b`. -/
def heqGoalArgs (g : MVarId) : MetaM (List Level × Array Expr) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``HEq 4 do throwError "the goal is not a heterogeneous equality"
  return (t.getAppFn.constLevels!, t.getAppArgs)

end Stacks.HEqCongr

open Stacks.HEqCongr in
/-- Close a goal `HEq a b` in which `a` and `b` are the same morphism up to proofs and up to the
spelling of the objects and categories they mention.  See `Stacks.HEqCongr.heqByCongr`. -/
elab "heq_congr" : tactic => withMainContext do
  let g ← getMainGoal
  let (_, args) ← heqGoalArgs g
  g.assign (← heqByCongr args[1]! args[3]!)
  replaceMainGoal []

open Stacks.HEqCongr in
/-- Close a goal `HEq a b` in which `a` and `b` are the same term up to proofs and up to the
spelling of the objects, categories and instances they mention, by congruence through every
common head.  See `Stacks.HEqCongr.heqFullAux`. -/
elab "heq_congr_full" : tactic => withMainContext do
  let g ← getMainGoal
  let (_, args) ← heqGoalArgs g
  let cache ← IO.mkRef {}
  let ccache ← IO.mkRef {}
  g.assign (← heqFullAux cache ccache 512 args[1]! args[3]!).1
  replaceMainGoal []

open Stacks.HEqCongr in
/-- Turn a goal `HEq (G.map (f ≫ g)) b` into `HEq (G.map f ≫ G.map g) b`, by
`CategoryTheory.Functor.map_comp` with the arguments read off the goal. -/
elab "heq_split_map_comp" : tactic => withMainContext do
  let g ← getMainGoal
  let (lvl, args) ← heqGoalArgs g
  let lhs := args[1]!
  unless lhs.isAppOfArity `CategoryTheory.Functor.map 8 do
    throwError "heq_split_map_comp: the left-hand side is not the image of a morphism"
  let la := lhs.getAppArgs
  let k := la[7]!
  unless k.isAppOfArity `CategoryTheory.CategoryStruct.comp 7 do
    throwError "heq_split_map_comp: the left-hand side is not the image of a composite"
  let ka := k.getAppArgs
  let mapComp := mkAppN (mkConst `CategoryTheory.Functor.map_comp lhs.getAppFn.constLevels!)
    #[la[0]!, la[1]!, la[2]!, la[3]!, la[4]!, ka[2]!, ka[3]!, ka[4]!, ka[5]!, ka[6]!]
  let eqArgs := (← inferType mapComp).getAppArgs
  let lhsMC := eqArgs[1]!
  let rhs' := eqArgs[2]!
  let ty' ← inferType rhs'
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp4 (mkConst ``HEq lvl) ty' rhs' args[2]! args[3]!)
  let h1 := mkAppN (mkConst ``HEq.trans lvl) #[args[0]!, args[0]!, ty', lhs, lhsMC, rhs',
    ← heqByCongr lhs lhsMC, mkApp4 (mkConst ``heq_of_eq lvl) args[0]! lhsMC rhs' mapComp]
  g.assign (mkAppN (mkConst ``HEq.trans lvl)
    #[args[0]!, ty', args[2]!, lhs, rhs', args[3]!, h1, g'])
  replaceMainGoal [g'.mvarId!]

end
