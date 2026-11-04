module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover

/-!
# `Proj R[T₀, …, Tₙ]` is smooth over `R`

Grade `R[T₀, …, Tₙ]` by total degree. The structure morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R` is
smooth, and so is the coefficient inclusion `R → R[T]_{(Tᵢ)}` into each chart ring.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.smooth_coeffToAway`: the coefficient inclusion of `R`
  into a chart ring is a smooth ring homomorphism.
* `Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff`: the structure morphism of the
  polynomial model of projective `n`-space is smooth.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The member of the standard affine cover indexed by `i` is the standard chart `D₊(Tᵢ)`. -/
public theorem affineChartCover_openCover_f (i : Fin (n + 1)) :
    (affineChartCover R n).openCover.f i =
      AlgebraicGeometry.Proj.awayι (polyGrading R n) (MvPolynomial.X i)
        (X_mem_one R n i) Nat.one_pos :=
  rfl

/-- The coefficient inclusion into a chart ring factors through the polynomial ring on the
affine coordinates. -/
public theorem chartHom_comp_C (i : Fin (n + 1)) :
    (chartHom R n i).comp
        (MvPolynomial.C : R →+* MvPolynomial {j : Fin (n + 1) // j ≠ i} R) =
      coeffToAway R n i :=
  RingHom.ext (chartHom_C R n i)

/-- **The coefficient inclusion `R → R[T]_{(Tᵢ)}` is smooth.** -/
public theorem smooth_coeffToAway (i : Fin (n + 1)) :
    RingHom.Smooth (coeffToAway R n i) := by
  rw [← chartHom_comp_C R n i]
  refine RingHom.Smooth.comp ?_ (RingHom.Smooth.of_bijective
    ⟨chartHom_injective R n i, chartHom_surjective R n i⟩)
  rw [← MvPolynomial.algebraMap_eq R {j : Fin (n + 1) // j ≠ i}]
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- **The polynomial model of projective `n`-space is smooth over its base.** The structure
morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R` is smooth. -/
public theorem smooth_projToSpecCoeff : AlgebraicGeometry.Smooth (projToSpecCoeff R n) := by
  let _ : AlgebraicGeometry.IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  have h : ∀ i : Fin (n + 1), AlgebraicGeometry.Smooth
      (AlgebraicGeometry.Proj.awayι (polyGrading R n) (MvPolynomial.X i)
        (X_mem_one R n i) Nat.one_pos ≫ projToSpecCoeff R n) := fun i => by
    rw [ProjBaseChange.awayι_comp_projToSpecCoeff]
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).2 (smooth_coeffToAway R n i)
  exact AlgebraicGeometry.IsZariskiLocalAtSource.of_openCover
    (affineChartCover R n).openCover h

end Stacks.AlgebraicGeometry.ProjPolyChart

end
