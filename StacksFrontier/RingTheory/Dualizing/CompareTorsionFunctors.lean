module

public import StacksFrontier.AlgebraicGeometry.LocalCohomologyDualizing.Basic
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor

/-!
# Characterization of the comparison of derived torsion and local cohomology

Let `I` be a finitely generated ideal of a commutative ring `A` and `Z = V(I)`. There are two
functors from `D(A)` to the full subcategory `D_{I^∞-torsion}(A)`: derived `I`-power torsion
`RΓ_I`, composed with the comparison of Stacks Tag 0A6N, and local cohomology `RΓ_Z`, the right
adjoint of the inclusion. The second is universal among objects with `I`-power-torsion
cohomology mapping to a given object, so the canonical derived torsion map `RΓ_I → id`
factors uniquely through its counit. Those factorizations are the components of
`Dualizing.compareTorsionFunctors`, constructed in
`StacksFrontier.AlgebraicGeometry.LocalCohomologyDualizing.Basic`; this file records the
factorization property of its components and the uniqueness that pins them down.

## Main results

* `Dualizing.compareTorsionFunctors_app_counit` — each component factors the canonical derived
  torsion map through the local cohomology counit.
* `Dualizing.compareTorsionFunctors_app_unique` — that factorization property determines the
  component.

## Implementation notes

The derived torsion map used here is `Dualizing.derivedPowerTorsionCounit`, the counit of the
adjunction of Stacks Tag 0A6L normalized by the underived torsion-submodule inclusion. The
module universe is enlarged to `max u v` to match the construction of `RΓ_I`.

## References

* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The comparison factors the canonical derived torsion map through the local cohomology
counit. -/
theorem compareTorsionFunctors_app_counit
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedPowerTorsionProperty A I hI).ι.map
        ((compareTorsionFunctors.{u, v} A I hI).app K) ≫
        (localCohomologyAdjunction.{u, max u v} A I hI).counit.app K =
      (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
          ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
        (derivedPowerTorsionCounit.{u, v} A I hI).app K :=
  ((compareTorsionFunctorsData.{u, v} A I hI).2 K).1

/-- Every factorization of the canonical derived torsion map through the local cohomology counit
is the corresponding component of the comparison. -/
theorem compareTorsionFunctors_app_unique
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (f : (derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI).obj K ⟶
      (localCohomologyFunctor.{u, max u v} A I hI).obj K)
    (hf : (derivedPowerTorsionProperty A I hI).ι.map f ≫
        (localCohomologyAdjunction.{u, max u v} A I hI).counit.app K =
      (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
          ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
        (derivedPowerTorsionCounit.{u, v} A I hI).app K) :
    f = (compareTorsionFunctors.{u, v} A I hI).app K :=
  ((compareTorsionFunctorsData.{u, v} A I hI).2 K).2 f hf

end Dualizing
