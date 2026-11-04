module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.CohomologicalDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.FinitePushforwardInputs
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent from the fppf to the small étale site (Stacks 0DDT)

Let `B` be a big fppf site, `X` an object of it, and `a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` the
composite of the change of topology `ε_X : (Sch/X)_fppf ⟶ (Sch/X)_étale` and the projection
`π_X : (Sch/X)_étale ⟶ X_étale`. This file proves Stacks 0DDT: for `K` in `D⁺(X_étale)` the map

`K ⟶ Ra_{X,*} a_X^{-1} K`

is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_app`: **Stacks 0DDT**.

## The proof

As in the source, through `AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite`:
Leray's acyclicity lemma (Stacks 015E) reduces to a single sheaf `F`, where
`a_{X,*}a_X^{-1}F = F` by Stacks 0DDL and `R^q a_{X,*}(a_X^{-1}F) = 0` for `q > 0` by
Stacks 0DDS (1) and the exactness of `π_{X,*}` (Stacks 0DDI). The two facts about the direct
image along a finite morphism that Stacks 0DDS (1) uses are those of the proof of Stacks 0DDJ (4),
supplied by `AlgebraicGeometry.fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite`
(exactness of `f_{big,*}`) and `AlgebraicGeometry.fppfEtaleWeakSerre_overMapPushforward_of_finite`
(`f_{big,*}π_X⁻¹F = π_Y⁻¹f_{small,*}F`, Stacks 0959).

The derived categories are arbitrary models: the statement carries `HasDerivedCategory`
instances for the two sheaf categories.

## References

* [Stacks Project, Tag 0DDT](https://stacks.math.columbia.edu/tag/0DDT)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (X : B.Schemes)
  [HasDerivedCategory
    (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (B.topology.over X) AddCommGrpCat.{u + 1})]

/-- **Stacks 0DDT.** Let `X` be a scheme, an object of a big fppf site `B`, and
`a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` the morphism of topoi to its small étale site. For `K` in
`D⁺(X_étale)` the map `K ⟶ Ra_{X,*}a_X^{-1}K`, the component at `K` of the derived unit of
`a_X^{-1} ⊣ a_{X,*}` (`AlgebraicGeometry.fppfSmallEtaleAdjunctionDerivedUnit`), is an
isomorphism. -/
@[stacks 0DDT]
theorem isIso_fppfSmallEtaleAdjunctionDerivedUnit_app
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})) :
    IsIso ((fppfSmallEtaleAdjunctionDerivedUnit B X).app K) :=
  have := isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite (X := X)
    fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite
    fppfEtaleWeakSerre_overMapPushforward_of_finite
  inferInstance

end AlgebraicGeometry
