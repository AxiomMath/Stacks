module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain

/-!
# The standard chart of `Proj R[T]` is the base change of the standard chart of the integral model

The ring half of the comparison of the two models of projective space. Coefficient change on a
polynomial ring is a pushout square of commutative rings, and under the identification of the
standard affine chart `R[T]_{(Tᵢ)}` with a polynomial ring on the affine coordinates
(`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`) the chart square inherits that property.

## Main results

* `Stacks.AlgebraicGeometry.ProjBaseChange.isPushout_mvPolynomial_map`: coefficient change
  `R₀[Y] → R[Y]` is a pushout of `R₀ → R` along `R₀ → R₀[Y]`.
* `Stacks.AlgebraicGeometry.ProjBaseChange.isPushout_chartBaseChange`: the same for the standard
  affine chart of `Proj` of a polynomial ring, with the coefficient change of
  `Stacks.AlgebraicGeometry.ProjPolyChart.chartBaseChange`.

## Implementation notes

The pushout of rings is obtained from `CommRingCat.isPushout_tensorProduct` and
`MvPolynomial.algebraTensorAlgEquiv`, which identifies `R ⊗_{R₀} R₀[Y]` with `R[Y]`. The algebra
structure of `R` over `R₀` is the one attached to the coefficient homomorphism by
`RingHom.toAlgebra`, supplied as a local instance inside the proof; no such instance exists
globally, and in the application the coefficient ring is the universe copy `ULift ℤ` of the
integers, for which it certainly does not.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.AlgebraicGeometry.ProjBaseChange

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Coefficient change on a polynomial ring is a pushout.** The polynomial ring over `R` is the
base change along `R₀ → R` of the polynomial ring over `R₀`. -/
public theorem isPushout_mvPolynomial_map {R₀ R : Type u} [CommRing R₀] [CommRing R]
    (κ : R₀ →+* R) (Y : Type) :
    IsPushout (CommRingCat.ofHom κ)
      (CommRingCat.ofHom (MvPolynomial.C : R₀ →+* MvPolynomial Y R₀))
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial Y R))
      (CommRingCat.ofHom (MvPolynomial.map κ)) := by
  let _ := κ.toAlgebra
  refine (CommRingCat.isPushout_tensorProduct R₀ R (MvPolynomial Y R₀)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (MvPolynomial.algebraTensorAlgEquiv R₀ R).toRingEquiv.toCommRingCatIso rfl ?_ ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    simp
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    simp [RingEquiv.toCommRingCatIso, Algebra.TensorProduct.includeLeftRingHom,
      MvPolynomial.smul_eq_C_mul]
  · refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp [RingEquiv.toCommRingCatIso, RingHom.algebraMap_toAlgebra]

/-- **The chart square of coefficient change is a pushout.** The standard affine chart of
`Proj R[T]` at `Tᵢ` is the base change along `R₀ → R` of the standard affine chart of
`Proj R₀[T]` at `Tᵢ`. -/
public theorem isPushout_chartBaseChange {R₀ R : Type u} [CommRing R₀] [CommRing R]
    (κ : R₀ →+* R) (n : ℕ) (i : Fin (n + 1)) :
    IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (coeffToAway R₀ n i))
      (CommRingCat.ofHom (coeffToAway R n i))
      (CommRingCat.ofHom (chartBaseChange R₀ n κ i)) :=
  (isPushout_mvPolynomial_map κ {j : Fin (n + 1) // j ≠ i}).of_iso
    (Iso.refl _) (Iso.refl _) (chartEquiv R₀ n i).toCommRingCatIso
    (chartEquiv R n i).toCommRingCatIso rfl
    (CommRingCat.hom_ext (RingHom.ext fun r => by
      simp [RingEquiv.toCommRingCatIso]))
    (CommRingCat.hom_ext (RingHom.ext fun r => by
      simp [RingEquiv.toCommRingCatIso]))
    (CommRingCat.hom_ext (RingHom.ext fun p => by
      simpa [RingEquiv.toCommRingCatIso] using (chartBaseChange_chartHom R₀ n κ i p).symm))

end Stacks.AlgebraicGeometry.ProjBaseChange

end
