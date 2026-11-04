module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# Projective `n`-space is smooth of relative dimension `n`

On the standard chart `D₊(Tᵢ)` the structure morphism of `Proj R[T₀, …, Tₙ]` to `Spec R` is
`Spec` of the coefficient inclusion `R → R[T]_{(Tᵢ)}`, which is the inclusion of `R` into a
polynomial ring in the `n` affine coordinates followed by a ring isomorphism. A polynomial ring
in `n` variables is standard smooth of relative dimension `n`, so the structure morphism is
smooth of relative dimension `n`; projective `n`-space over any scheme `S` is a base change of
the integral model, and smoothness of relative dimension `n` is stable under base change.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff`: the
  polynomial model `Proj R[T₀, …, Tₙ] ⟶ Spec R` is smooth of relative dimension `n`.
* `AlgebraicGeometry.projectiveSpaceOver.smoothOfRelativeDimension`: `ℙⁿ_S ⟶ S` is smooth of
  relative dimension `n`.

## Implementation notes

As for `Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff`, the instance of
`AlgebraicGeometry.IsZariskiLocalAtSource` for the property is supplied by hand, since instance
search cannot find the ring-homomorphism property it is associated with.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The coefficient inclusion of `R` into a chart ring is standard smooth of relative
dimension `n`.** It is the inclusion of `R` into the polynomial ring on the `n` affine
coordinates, followed by a ring isomorphism. -/
public theorem isStandardSmoothOfRelativeDimension_coeffToAway (i : Fin (n + 1)) :
    (coeffToAway R n i).IsStandardSmoothOfRelativeDimension n := by
  rw [← chartHom_comp_C R n i]
  have e : {j : Fin (n + 1) // j ≠ i} ≃ Fin n := Fintype.equivFinOfCardEq (by simp)
  have h1 : (MvPolynomial.C : R →+* MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
      |>.IsStandardSmoothOfRelativeDimension n := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n
      (MvPolynomial.renameEquiv R e.symm)
  have h := (RingHom.IsStandardSmoothOfRelativeDimension.equiv (RingEquiv.ofBijective
    (chartHom R n i) ⟨chartHom_injective R n i, chartHom_surjective R n i⟩)).comp h1
  rwa [Nat.zero_add] at h

/-- **The polynomial model of projective `n`-space is smooth of relative dimension `n`.** -/
public theorem smoothOfRelativeDimension_projToSpecCoeff :
    SmoothOfRelativeDimension n (projToSpecCoeff R n) := by
  let _ : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  have h : ∀ i : Fin (n + 1), SmoothOfRelativeDimension n
      (Proj.awayι (polyGrading R n) (MvPolynomial.X i) (X_mem_one R n i) Nat.one_pos ≫
        projToSpecCoeff R n) := fun i => by
    rw [ProjBaseChange.awayι_comp_projToSpecCoeff,
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      (isStandardSmoothOfRelativeDimension_coeffToAway R n i)
  exact IsZariskiLocalAtSource.of_openCover (affineChartCover R n).openCover h

end Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ProjPolyChart

/-- The integral model of projective `n`-space is smooth of relative dimension `n` over the
terminal scheme. -/
public theorem smoothOfRelativeDimension_terminalFrom_projectiveSpaceAtUniverse (n : ℕ) :
    SmoothOfRelativeDimension n (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have := smoothOfRelativeDimension_projToSpecCoeff (ULift.{u} ℤ) n
  have h : SmoothOfRelativeDimension (n + 0) (projToSpecCoeff (ULift.{u} ℤ) n ≫
      terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) := inferInstance
  rwa [Nat.add_zero, show projToSpecCoeff (ULift.{u} ℤ) n ≫
      terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) =
      terminal.from (projectiveSpaceAtUniverse.{u} n) from terminalIsTerminal.hom_ext _ _] at h

namespace projectiveSpaceOver

/-- **Projective `n`-space over a scheme `S` is smooth of relative dimension `n` over `S`.** It
is the base change of the integral model. -/
public instance smoothOfRelativeDimension (n : ℕ) (S : Scheme.{u}) :
    SmoothOfRelativeDimension n (projectiveSpaceOver n S ↘ S) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
    (smoothOfRelativeDimension_terminalFrom_projectiveSpaceAtUniverse n)

end projectiveSpaceOver

end AlgebraicGeometry

end
