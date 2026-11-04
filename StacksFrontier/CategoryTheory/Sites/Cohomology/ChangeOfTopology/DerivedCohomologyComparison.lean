module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedUnitCommShift

/-!
# The change-of-topology map on hypercohomology

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3, let `X` be an
object of `C` and write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology morphism. Stacks 0EZB
compares, for a bounded below object `L` of `D(C_{τ'}/X)`, the two cohomologies

`H^m_{τ'}(X, L)` and `H^m_τ(X, ε_X^{-1}L)`.

This file constructs the map between them, as a natural transformation of functors on bounded
below derived categories:

`RΓ_{τ'}(X, -) ⟶ (ε_X^{-1})_{D⁺} ⋙ RΓ_τ(X, -)`.

Both ingredients are already present. The canonical map `L ⟶ Rε_{X,*}(ε_X^{-1}L)` is
`Stacks.ComparingTopologies.derivedComparisonUnit`, and applying `RΓ_{τ'}(X, -)` to it lands in
`RΓ_{τ'}(X, Rε_{X,*}(ε_X^{-1}L))`, which is `RΓ_τ(X, ε_X^{-1}L)` by the instance of Stacks 0D6H
proved in `DerivedGlobalSections`, `derivedGlobalSectionsComparisonPlusIso`. So the map is the
composite of the two, and nothing is chosen.

## Main definitions

* `Stacks.ComparingTopologies.derivedCohomologyComparison`: the natural transformation above.

## Main results

* `Stacks.ComparingTopologies.isIso_derivedCohomologyComparison_app_of_isIso`: the comparison is
  invertible at an object where the derived unit `L ⟶ Rε_{X,*}(ε_X^{-1}L)` is invertible, the
  other two factors being an associator and an isomorphism. This is the reduction of Stacks 0EZB
  to clause (1) of Stacks 0EZF.

## What this file does not contain

Stacks 0EZB itself, which asserts that the comparison is invertible on `H^n` as soon as `(V_n)`
holds and the cohomology sheaves `H^i(L)` lie in `𝒜'_X` for `0 ≤ i ≤ n`. That is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparingCohomology`, as
`Stacks.ComparingTopologies.isIso_homology_derivedCohomologyComparison`, by dévissage along the
truncation triangles rather than through the degreewise comparison `cohomologyComparison` of
`ChangeOfTopology.Cohomology`; so the identification of the two constructions, which earlier
drafts of this docstring recorded as owed, is not needed and is still not available.

## References

* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

/-- **The change-of-topology map on the cohomology of a bounded below object,**

`RΓ_{τ'}(X, L) ⟶ RΓ_τ(X, ε_X^{-1}L)`,

natural in `L` in the bounded below derived category of abelian sheaves on `C_{τ'}/X`. It is
`RΓ_{τ'}(X, -)` applied to the canonical map `L ⟶ Rε_{X,*}(ε_X^{-1}L)` of
`Stacks.ComparingTopologies.derivedComparisonUnit`, read through the identification
`Rε_{X,*} ⋙ RΓ_{τ'}(X, -) ≅ RΓ_τ(X, -)` of
`Stacks.ComparingTopologies.derivedGlobalSectionsComparisonPlusIso`, the instance of
Stacks 0D6H for a change of topology. Its effect on `H^m` is the map
`H^m_{τ'}(X, L) ⟶ H^m_τ(X, ε_X^{-1}L)` compared by Stacks 0EZB. -/
def derivedCohomologyComparison (S : CohomologyComparison C) (X : C) :
    (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus ⟶
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
        (globalSectionsOver S.fineCoverage.toGrothendieck X).rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedComparisonUnit S X)
      (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus ≫
    (Functor.associator
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus
      (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus).hom ≫
    Functor.whiskerLeft
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus
      (derivedGlobalSectionsComparisonPlusIso S X).hom

/-- **The comparison on cohomology is invertible at an object where the derived unit
`L ⟶ Rε_{X,*}(ε_X^{-1}L)` is invertible.** The other two factors of the comparison are an
associator and the isomorphism of Stacks 0D6H, so nothing beyond the invertibility of the unit
is needed; this is the reduction of Stacks 0EZB to clause (1) of Stacks 0EZF. -/
instance isIso_derivedCohomologyComparison_app_of_isIso (S : CohomologyComparison C) (X : C)
    (L : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    [IsIso ((derivedComparisonUnit S X).app L)] :
    IsIso ((derivedCohomologyComparison S X).app L) := by
  dsimp only [derivedCohomologyComparison]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

end Stacks.ComparingTopologies

end
