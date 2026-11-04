module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhTorsionComparison

/-!
# The ph direct image of the pullback of a torsion complex (Stacks 0DE5)

Let `B` be a big ph site, `X` an object of it, `ε_X : Sh((Sch/X)_ph) ⟶ Sh((Sch/X)_étale)` the
change of topology, `π_X : Sh((Sch/X)_étale) ⟶ Sh(X_étale)` the projection to the small étale site
and `a_X = π_X ∘ ε_X`. For `K` in `D⁺(X_étale)` with torsion cohomology sheaves the canonical map
`K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_phEtaleTorsionDerivedSmallEtaleUnit`: for `K` in `D⁺(X_étale)` with
  torsion cohomology sheaves, the map `K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism.

## Implementation notes

The map is `AlgebraicGeometry.derivedSmallEtaleFineUnit`: the derived unit `K ⟶ Rπ_{X,*}π_X⁻¹K`
of `π_X⁻¹ ⊣ π_{X,*}` (invertible by Stacks 0DDI), followed by `Rπ_{X,*}` of the derived unit
`π_X⁻¹K ⟶ Rε_{X,*}ε_X⁻¹π_X⁻¹K` of the change of topology and the identification
`Rπ_{X,*} ∘ Rε_{X,*} = Ra_{X,*}`, `π_{X,*}` being exact. The middle factor is invertible by
Stacks 0DE4 (3); this is the Leray argument of the source's proof, the reduction to a single sheaf
being built into the derived comparison of Stacks 0EZA. The comparison situation is
`AlgebraicGeometry.phEtaleTorsionComparison` (Stacks 0F0I), whose inputs are the proper base
change theorems Stacks 0A3U (for sheaves of sets) and Stacks 095T.

Objects of the big ph site are the schemes `X` of the statement; every scheme is one, for a
suitable big ph site.

## References

* [Stacks Project, Tag 0DE5](https://stacks.math.columbia.edu/tag/0DE5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigPHSite.{u})

/-- The category of abelian sheaves on the small étale site of an object `X` of the big ph site
is Grothendieck abelian. -/
local instance (X : (phAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

/-- For an object `X` of the big ph site and `K` in `D⁺(X_étale)` with torsion cohomology
sheaves, the map `K ⟶ Ra_{X,*}a_X⁻¹K` is an isomorphism, where
`a_X = π_X ∘ ε_X : Sh((Sch/X)_ph) ⟶ Sh(X_étale)`; the map is
`AlgebraicGeometry.derivedSmallEtaleFineUnit`, the unit of `a_X⁻¹ ⊣ a_{X,*}` on `D⁺`. -/
@[stacks 0DE5]
public theorem isIso_phEtaleTorsionDerivedSmallEtaleUnit (X : (phAssociatedBigEtaleSite B).Scheme)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso (derivedSmallEtaleFineUnit (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph B X.1 X.2 F).1)
      (properDirectImageComparison _) (BigPHSite.exists_properRefinement B) X K) :=
  isIso_derivedSmallEtaleFineUnit _ _ _ _ _ _ X K hK

end AlgebraicGeometry

end
