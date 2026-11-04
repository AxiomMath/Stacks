module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.HCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.HComparisonSituation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleChangeOfTopology
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.HSitePrecoverage
import StacksCore.Tactic.StacksAttribute

/-!
# Torsion sheaves pulled back from the small étale site to the big h site

Let `B` be a chosen big h site and `X` an object of it. Write `π_X` for the morphism from the big
étale topos over `X` to the small étale topos of `X`, `ε_X` for the comparison morphism from the
big h topos over `X` to the big étale topos over `X`, and `a_X = π_X ∘ ε_X`, so that
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. This file proves Stacks 0EWF: on torsion sheaves and on bounded below
complexes with torsion cohomology sheaves, `a_X⁻¹` does not change cohomology, and it commutes
with higher direct images along proper morphisms.

By Stacks 0F0J (`AlgebraicGeometry.hEtaleCohomologyComparison`) the general results of Cohomology
on Sites, Section 0EZ1, apply to the comparison of the h topology with the étale topology, with
the proper morphisms as distinguished class and the sheaves `π_X⁻¹F`, `F` a torsion abelian sheaf
on `X_étale`, as the classes `𝒜'_X`. The four parts of 0EWF are the instances at the h topology of
the corresponding statements for the étale topology and an arbitrary finer topology in such a
comparison situation.

## Main results

* `AlgebraicGeometry.hTorsionComparison_smallEtaleInclusion` — **Stacks 0EWF (1)**:
  `ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`.
* `AlgebraicGeometry.isIso_hTorsionHigherSmallEtaleBaseChange` — **Stacks 0EWF (2)**: for `f`
  proper, `a_Y⁻¹(R^i f_{small,*}F) = R^i f_{big,h,*}(a_X⁻¹F)` for all `i`.
* `AlgebraicGeometry.isIso_hTorsionDerivedComparisonUnit_app` — **Stacks 0EWF (3)**:
  `π_X⁻¹K ⟶ Rε_{X,*}(a_X⁻¹K)` is an isomorphism.
* `AlgebraicGeometry.isIso_hTorsionDerivedSmallEtaleBaseChange` — **Stacks 0EWF (4)**: for `f`
  proper, `a_Y⁻¹(Rf_{small,*}K) = Rf_{big,h,*}(a_X⁻¹K)`.

## Implementation notes

The étale topos over `X` and the small étale site of `X` are those of the big étale site
`AlgebraicGeometry.hAssociatedBigEtaleSite B` underlying `B`; the h topology over `X` is the
localization of `B.precoverage`. In parts (2) and (4) the equalities of the source are the
canonical base change maps of the square of topoi `a_Y ∘ f_h = f_small ∘ a_X`:
`AlgebraicGeometry.higherSmallEtaleFineBaseChange` and
`AlgebraicGeometry.derivedSmallEtaleFineBaseChange`. The inputs from the proper base change
theorem are the h sheaf condition of `π_X⁻¹F`, Stacks 0EW8
(`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_and_isIso_unit`, from Stacks 0A3U), and the
comparison of higher direct images of Stacks 0DDJ (2)
(`AlgebraicGeometry.BigHSite.properDirectImageComparison`, from
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, Stacks 095T).

Standard model: the derived categories are those of `HasDerivedCategory.standard`, in which the
change of topology results of Stacks 0EZF used here
(`Stacks.ComparingTopologies.derivedComparisonUnit`) are stated.

## References

* [Stacks Project, Tag 0EWF](https://stacks.math.columbia.edu/tag/0EWF)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ComparingTopologies
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigHSite.{u})

/-- The category of abelian sheaves on the small étale site of `X` is Grothendieck abelian. -/
local instance (X : (hAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

/-- For an object `X` of the big h site and an abelian torsion sheaf `F` on `X_étale`,
`ε_{X,*}a_X⁻¹F = π_X⁻¹F` — the unit `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F` of the change of topology is an
isomorphism — and `R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`. -/
@[stacks 0EWF "(1)"]
public theorem hTorsionComparison_smallEtaleInclusion (X : (hAssociatedBigEtaleSite B).Scheme)
    (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) F) :
    IsIso ((abelianComparisonAdjunction B.precoverage
        (hAssociatedBigEtaleSite B).precoverage
        (BigHSite.etalePrecoverage_le_precoverage B) X).unit.app
        (((SmallEtale.inclusion (hAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
          Ab.{u + 1} (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
          ((hAssociatedBigEtaleSite B).topology.over X)).obj F)) ∧
      ∀ i : ℕ, 0 < i → IsZero (((abelianComparisonPushforward B.precoverage
          (hAssociatedBigEtaleSite B).precoverage
          (BigHSite.etalePrecoverage_le_precoverage B) X).rightDerived i).obj
        ((abelianComparisonPullback B.precoverage
          (hAssociatedBigEtaleSite B).precoverage X).obj
          (((SmallEtale.inclusion (hAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            Ab.{u + 1} (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
            ((hAssociatedBigEtaleSite B).topology.over X)).obj F))) :=
  ⟨isIso_comparisonUnit_smallEtaleInclusion
      (hAssociatedBigEtaleSite B) B.precoverage
      (BigHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
      (BigHSite.properDirectImageComparison B)
      (BigHSite.exists_properRefinement B) X F hF,
    fun i hi => isZero_rightDerived_comparisonPushforward_smallEtaleInclusion
      (hAssociatedBigEtaleSite B) B.precoverage
      (BigHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
      (BigHSite.properDirectImageComparison B)
      (BigHSite.exists_properRefinement B) X F hF i hi⟩

/-- For a proper morphism `f : X ⟶ Y` of the big h site and an abelian torsion sheaf `F` on
`X_étale`, the base change map `a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{big,h,*}(a_X⁻¹F)` is an
isomorphism for every `i`. The map is `AlgebraicGeometry.higherSmallEtaleFineBaseChange`, the
degree `i` cohomology of the derived base change map
`AlgebraicGeometry.derivedSmallEtaleFineBaseChange` at `F` placed in degree zero. -/
@[stacks 0EWF "(2)"]
public theorem isIso_hTorsionHigherSmallEtaleBaseChange
    {X Y : (hAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((hAssociatedBigEtaleSite B).inclusion.map f))
    (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) F)
    (i : ℕ) :
    IsIso (higherSmallEtaleFineBaseChange (hAssociatedBigEtaleSite B) B.precoverage
      (BigHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
      (BigHSite.properDirectImageComparison B)
      (BigHSite.exists_properRefinement B) f F i) :=
  isIso_higherSmallEtaleFineBaseChange _ _ _ _ _ _
    (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) f hf F hF i

/-- For an object `X` of the big h site and `K` in `D⁺(X_étale)` with torsion cohomology sheaves,
the map `π_X⁻¹K ⟶ Rε_{X,*}(a_X⁻¹K)`, the derived unit of the change of topology at `π_X⁻¹K`, is an
isomorphism. -/
@[stacks 0EWF "(3)"]
public theorem isIso_hTorsionDerivedComparisonUnit_app (X : (hAssociatedBigEtaleSite B).Scheme)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedComparisonUnit (hEtaleCohomologyComparison B) X).app
      (((SmallEtale.inclusion (hAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
        Ab.{u + 1} (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
        ((hAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K)) :=
  isIso_derivedComparisonUnit_app_smallEtaleInclusion
    (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B)
    (BigHSite.exists_properRefinement B) X K hK

/-- For a proper morphism `f : X ⟶ Y` of the big h site and `K` in `D⁺(X_étale)` with torsion
cohomology sheaves, the base change map `a_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,h,*}(a_X⁻¹K)` of the
square of topoi `a_Y ∘ f_h = f_small ∘ a_X`, `AlgebraicGeometry.derivedSmallEtaleFineBaseChange`,
is an isomorphism. -/
@[stacks 0EWF "(4)"]
public theorem isIso_hTorsionDerivedSmallEtaleBaseChange
    {X Y : (hAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((hAssociatedBigEtaleSite B).inclusion.map f))
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso (derivedSmallEtaleFineBaseChange (hAssociatedBigEtaleSite B) B.precoverage
      (BigHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
      (BigHSite.properDirectImageComparison B)
      (BigHSite.exists_properRefinement B) f K) :=
  isIso_derivedSmallEtaleFineBaseChange _ _ _ _ _ _
    (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) f hf K hK

end AlgebraicGeometry

end
