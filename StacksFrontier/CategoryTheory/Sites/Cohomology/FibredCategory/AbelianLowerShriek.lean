module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.AbelianRestrictionExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek on abelian sheaves for a morphism of fibred categories

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and give `C` and `C'` the topologies they inherit from `D`. Stacks
06NW makes `u` continuous and cocontinuous for those topologies, so the induced morphism of topoi
`g : Sh(C') ⟶ Sh(C)` has inverse image `g^{-1} = u_s`, restriction along `u`.

This file is the abelian-sheaf half of the underived part of Stacks 08PC: `g^{-1}` on abelian
sheaves admits a left adjoint `g_!^{Ab}`, the two are exact and additive, and `g^{-1}` therefore
preserves finite limits and finite colimits. Those are the inputs the two forgetful squares of
Stacks 08PC parts (2) and (4) need on the abelian side, and the inputs from which the derived
functor `Lg_!^{Ab}` of part (3) is built.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.abelianInverseImage`: `g^{-1} : Ab(C) ⥤ Ab(C')`,
  restriction of abelian sheaves along `u`.
* `Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriek`: `g_!^{Ab} : Ab(C') ⥤ Ab(C)`,
  the chosen left adjoint of `g^{-1}`.
* `Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAdjunction`: the adjunction
  `g_!^{Ab} ⊣ g^{-1}`.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.abelianInverseImage_isRightAdjoint`: **Stacks
  08PC, part (1) for abelian sheaves.** `g^{-1}` admits a left adjoint.
* `Stacks.Sites.FibredCategory.MorphismSituation.abelianInverseImage_exact`: `g^{-1}` is exact.
* `Stacks.Sites.FibredCategory.MorphismSituation.abelianInverseImage_additive` and
  `Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriek_additive`: both functors are
  additive, which is what lets them be applied degreewise to complexes.

## Implementation notes

Nothing here uses the ringed structure of the base, the structure sheaves, or the commutative
diagram of ringed topoi: the inherited topologies, and the continuity and cocontinuity of `u` that
Stacks 08PA's `MorphismSituation` already carries, are the whole input. So the declarations take
the situation alone and not a `MorphismSituation.RingedToposDiagram`. The form in which Stacks
08PC states them is this one with the diagram's `uContinuous` field in place of the instance
`MorphismSituation.uContinuous`; the two agree, `CategoryTheory.Functor.IsContinuous` being a
`Prop`.

The existence of `g_!^{Ab}` is Mathlib's left Kan extension construction of the pullback of
sheaves, `CategoryTheory.Functor.sheafPullbackConstruction`, which needs only that abelian groups
can be sheafified on the target site. Exactness of `g^{-1}` is not formal in either direction and
is
`CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous`; cocontinuity
of `u` is used there and nowhere else in this file. Preservation of finite *limits* is however
free once `g_!^{Ab}` exists, `g^{-1}` being its right adjoint, and is recorded separately with
that lighter hypothesis so that a consumer needing only left exactness does not have to supply
the sheafification hypotheses of the exactness statement.

The universe of the sections is the one Stacks 08PC pins, `max w u₀ u₁ u₂ v₀ v₁ v₂`, and not a
free universe: the left Kan extension along `u.op` is indexed by comma categories built from the
two fibred categories, so abelian groups in a universe unrelated to theirs do not have the
colimits the construction of `g_!^{Ab}` needs.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 0796](https://stacks.math.columbia.edu/tag/0796)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- `g^{-1} : Ab(C) ⥤ Ab(C')`, the inverse image of abelian sheaves along the morphism of topoi
induced by the 1-morphism of fibred categories: restriction along `u`, which is a sheaf for the
inherited topology because `u` is continuous. -/
abbrev abelianInverseImage :
    Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.u.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.sourceTopology S.totalTopology

/-- **Stacks 08PC, part (1) for abelian sheaves.** The inverse image of abelian sheaves along `g`
admits a left adjoint `g_!^{Ab}`. The left adjoint is the sheafification of the left Kan extension
along `u.op`, so the only hypothesis is that abelian groups can be sheafified on the target
site. -/
@[stacks 08PC "part (1), abelian sheaves"]
instance abelianInverseImage_isRightAdjoint
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] :
    S.abelianInverseImage.IsRightAdjoint :=
  inferInstance

/-- `g_!^{Ab} : Ab(C') ⥤ Ab(C)`, the lower-shriek functor on abelian sheaves: the chosen left
adjoint of `g^{-1}`. -/
abbrev abelianLowerShriek
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] :
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.u.sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.totalTopology

/-- The adjunction `g_!^{Ab} ⊣ g^{-1}` of Stacks 08PC, part (1) for abelian sheaves. -/
abbrev abelianLowerShriekAdjunction
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] :
    S.abelianLowerShriek ⊣ S.abelianInverseImage :=
  S.u.sheafAdjunctionContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.sourceTopology S.totalTopology

/-- The inverse image of abelian sheaves along `g` is additive: on underlying presheaves it is
restriction along `u.op`, which reindexes the components of a natural transformation. -/
instance abelianInverseImage_additive : S.abelianInverseImage.Additive :=
  inferInstance

/-- The lower-shriek functor on abelian sheaves is additive, being a left adjoint of the additive
functor `g^{-1}`. This is what lets it be applied degreewise to complexes of abelian sheaves. -/
instance abelianLowerShriek_additive
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] :
    S.abelianLowerShriek.Additive :=
  inferInstance

/-- The inverse image of abelian sheaves along `g` preserves finite limits: it is the right
adjoint of `g_!^{Ab}`. No exactness input is needed for this half, only the existence of the
lower-shriek functor. -/
instance abelianInverseImage_preservesFiniteLimits
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] :
    PreservesFiniteLimits S.abelianInverseImage :=
  inferInstance

section Exactness

variable [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-- **The inverse image of abelian sheaves along `g` is exact.** Left exactness holds for any
continuous functor of sites; right exactness is where cocontinuity of `u` enters, through the fact
that restriction commutes with sheafification. -/
theorem abelianInverseImage_exact : exactFunctor _ _ S.abelianInverseImage :=
  CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous
    S.sourceTopology S.totalTopology S.u

end Exactness

end Stacks.Sites.FibredCategory.MorphismSituation

end
