module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.HComparisonSituation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleChangeOfTopology
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing h and étale cohomology of torsion sheaves: Stacks 0EWG

Let `B` be a chosen big h site and `X` one of its schemes. Write `π_X` for the projection from the
big étale site over `X` to the small étale site of `X`, `ε_X` for the change of topology from the
étale to the h topology on the big site over `X`, and `a_X = π_X ∘ ε_X`. For `K` in
`D⁺(X_étale)` with torsion cohomology sheaves, the map `K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.hDerivedSmallEtaleUnit` — the map `K ⟶ Ra_{X,*}a_X⁻¹K`.

## Main results

* `AlgebraicGeometry.isIso_hDerivedSmallEtaleUnit` — for `K` with torsion cohomology sheaves,
  the map `K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism.

## Implementation notes

The map is `AlgebraicGeometry.derivedSmallEtaleFineUnit` for the h precoverage, in the comparison
situation `AlgebraicGeometry.hEtaleCohomologyComparison` of Stacks 0F0J. Its source is the
unit `K ⟶ Rπ_{X,*}π_X⁻¹K`, followed by `Rπ_{X,*}` of the derived change-of-topology unit
`π_X⁻¹K ⟶ Rε_{X,*}ε_X⁻¹π_X⁻¹K`, and by `Rπ_{X,*} ∘ Rε_{X,*} = R(π_{X,*} ∘ ε_{X,*})`. The first map
is invertible by Stacks 0DDI and the second by Stacks 0EZF (1), since `π_X⁻¹K` lies in
`D⁺_{𝒜'_X}`. This is the argument of the source rearranged: the source reduces to a single
torsion sheaf (Stacks 0DD7, 015E) and then uses the Leray spectral sequence of `a_X = π_X ∘ ε_X`
(Stacks 0734) with Stacks 0EWF (1) and 0DDI; here the reduction to sheaves and the Leray argument
are carried out once, on `D⁺`, inside Stacks 0EZF.

The derived categories are those of `HasDerivedCategory.standard`, the model in which Stacks 0EZF
and the comparison of the change of topology are stated.

## References

* [Stacks Project, Tag 0DDI](https://stacks.math.columbia.edu/tag/0DDI)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EWF](https://stacks.math.columbia.edu/tag/0EWF)
* [Stacks Project, Tag 0EWG](https://stacks.math.columbia.edu/tag/0EWG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigHSite.{u})

/-- The category of abelian sheaves on the small étale site of `X` is Grothendieck abelian. -/
local instance (X : (hAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

/-- The map `K ⟶ Ra_{X,*}a_X⁻¹K` for `K` in `D⁺(X_étale)`, where `a_X = π_X ∘ ε_X` is the
morphism from the big h topos over `X` to the small étale topos of `X`: the inverse image `a_X⁻¹`
is `π_X⁻¹` followed by h sheafification `ε_X⁻¹`, and `Ra_{X,*}` is the right derived functor of
the direct image `π_{X,*} ∘ ε_{X,*}` on abelian sheaves. -/
public def hDerivedSmallEtaleUnit (X : (hAssociatedBigEtaleSite B).Scheme)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})) :=
  derivedSmallEtaleFineUnit (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B) (BigHSite.exists_properRefinement B) X K

/-- Let `X` be a scheme, an object of a big h site `B`. For `K` in `D⁺(X_étale)` with torsion
cohomology sheaves, the map `K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism, with
`a_X : Sh((Sch/X)_h) ⟶ Sh(X_étale)` the composite of the change of topology
`ε_X : Sh((Sch/X)_h) ⟶ Sh((Sch/X)_étale)` and the projection
`π_X : Sh((Sch/X)_étale) ⟶ Sh(X_étale)`. -/
@[stacks 0EWG]
public theorem isIso_hDerivedSmallEtaleUnit (X : (hAssociatedBigEtaleSite B).Scheme)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso (hDerivedSmallEtaleUnit B X K) :=
  isIso_derivedSmallEtaleFineUnit (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B) (BigHSite.exists_properRefinement B) X K hK

end AlgebraicGeometry

end
