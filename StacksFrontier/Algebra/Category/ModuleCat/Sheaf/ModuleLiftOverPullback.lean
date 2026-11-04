module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift

/-!
# Lifting restriction to a slice site to sheaves of `Λ`-modules

Let `J` be a Grothendieck topology on a category `C` and let `U : C`. Restriction of sheaves to
the localized site `C/U` is `CategoryTheory.GrothendieckTopology.overPullback`; on sections it is
precomposition with `(Over.forget U).op`, so on abelian sheaves it is additive and may be fed to
`Stacks.ModuleCatLift.moduleLift`. This file identifies the lift of that restriction with
restriction of sheaves of `Λ`-modules: lifting and restricting commute on the nose.

## Main results

* `Stacks.ModuleCatLift.moduleLift_overPullback` — the lift of
  `J.overPullback AddCommGrpCat U` to sheaves of `Λ`-modules *is*
  `J.overPullback (ModuleCat Λ) U`, an equality of functors.
* `Stacks.ModuleCatLift.moduleLiftOverPullbackIso` — the same identification read as an
  isomorphism of functors, for use where an isomorphism is what a consumer expects.

The additivity of restriction, `Stacks.ModuleCatLift.overPullback_additive`, is supplied here as
an instance; it is what makes `Stacks.ModuleCatLift.moduleLift` applicable to restriction at all.

## Implementation notes

The coefficient ring `Λ` is an arbitrary ring, not a commutative one, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EndActionLift.lean`: multiplication by a scalar is
used only as an endomorphism of the underlying abelian sheaf.

Both comparisons are `rfl`. `J.overPullback A U` is
`CategoryTheory.Functor.sheafPushforwardContinuous` along `Over.forget U`, i.e. precomposition
with `(Over.forget U).op` on sections, and `Stacks.ModuleCatLift.ofEndAction` of a precomposition
with the whiskered scalar action is the precomposition of the original presheaf of `Λ`-modules:
the sections at `V : (Over U)ᵒᵖ` are the sections of the original sheaf at `V.unop.left` with
their own `Λ`-action, and the restriction maps are the original ones. Since
`CategoryTheory.Presheaf.IsSheaf` is a `Prop`, no further data has to be matched, so the two
functors are equal and not merely isomorphic.

The two `CategoryTheory.GrothendieckTopology.HasSheafCompose` hypotheses — one for `J` and one
for `J.over U` — are taken as instance arguments, as in `EndActionLift.lean`; they are the price
of naming the forgetful functor on sheaves and are discharged by the consumer.

Nothing here carries a `stacks` attribute: this is formal category theory feeding a result that
is tagged elsewhere, namely the extension of locally constant sheaves of modules to a slice site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁

namespace Stacks.ModuleCatLift

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (U : C)

/-- Restriction of abelian sheaves to the localized site `C/U` is additive: on sections it is
precomposition with `(Over.forget U).op`, and addition of morphisms of sheaves is computed
sectionwise. -/
public instance overPullback_additive :
    (J.overPullback AddCommGrpCat.{w} U).Additive where
  map_add := rfl

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **Lifting restriction is restricting the lift.** The lift to sheaves of `Λ`-modules of
restriction of abelian sheaves to the localized site `C/U` is restriction of sheaves of
`Λ`-modules to `C/U`, on the nose: both take a sheaf to its sections over the objects of `C/U`
with their original `Λ`-action. -/
public lemma moduleLift_overPullback :
    moduleLift Λ J (J.over U) (J.overPullback AddCommGrpCat.{w} U)
      = J.overPullback (ModuleCat.{w} Λ) U :=
  rfl

/-- The identification of `Stacks.ModuleCatLift.moduleLift_overPullback` as an isomorphism of
functors. The isomorphism is the identity, the two functors being equal. -/
public def moduleLiftOverPullbackIso :
    moduleLift Λ J (J.over U) (J.overPullback AddCommGrpCat.{w} U)
      ≅ J.overPullback (ModuleCat.{w} Λ) U :=
  eqToIso (moduleLift_overPullback Λ J U)

end Stacks.ModuleCatLift

end
