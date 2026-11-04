module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Chart conditions on the Quot functor, with and without a model

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module, the standing data `AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR. The Quot
presheaf takes values one universe above the site, so a property of its morphism to `B` defined
through étale charts (Stacks 03MJ) can be asked in two ways: for the morphism of presheaves of
`Type (u + 1)` itself, with its charts read through `CategoryTheory.uliftYoneda`, or for the
morphism to `B` of a model of the Quot presheaf in the universe of the site. This file shows that
the two readings agree for every model.

## Main results

* `QuotSitePresheafModel.holdsOnEveryEtaleChartULift_quotSitePresheafToBase_iff`: a property of
  scheme morphisms holds on every étale chart of the morphism to `B` of the Quot presheaf exactly
  when it holds on every étale chart of the morphism to `B` of any model.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DM3](https://stacks.math.columbia.edu/tag/0DM3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.QuotSitePresheafModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : QuotSituation B S hS}

/-- **A chart condition on `Quot_{F/X/B} ⟶ B` does not see the choice of a model.** For every
model `M` of the Quot presheaf in the universe of the site and every property `P` of scheme
morphisms, `P` holds on every étale chart of the morphism to `B` of the Quot presheaf (charts
read through `CategoryTheory.uliftYoneda`) exactly when it holds on every étale chart of the
morphism `M ⟶ B`. -/
theorem holdsOnEveryEtaleChartULift_quotSitePresheafToBase_iff (P : MorphismProperty Scheme.{u})
    (M : QuotSitePresheafModel D) :
    HoldsOnEveryEtaleChartULift.{u + 1} B S hS P D.quotSitePresheafToBase ↔
      HoldsOnEveryEtaleChart B S hS P M.toBase := by
  rw [← holdsOnEveryEtaleChartULift_whiskerRight_iff.{u + 1} B S hS P M.toBase,
    M.whiskerRight_toBase]
  refine ⟨fun h => holdsOnEveryEtaleChartULift_precomp B S hS P M.iso.hom _ h, fun h => ?_⟩
  simpa using holdsOnEveryEtaleChartULift_precomp B S hS P M.iso.inv _ h

end AlgebraicGeometry.Space.QuotSitePresheafModel

end
