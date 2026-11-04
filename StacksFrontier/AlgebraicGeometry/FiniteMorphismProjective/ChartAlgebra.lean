module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away

/-!
# A module-finite algebra is a quotient of the standard affine chart of `Proj R[T₀, …, Tₙ]`

Let `A` be an `R`-algebra generated as an `R`-module by a family `a` indexed by the nonzero
variables of `R[T₀, …, Tₙ]`. The degree-zero homogeneous localization
`R[T]_{(T₀)}` is the polynomial ring `R[Y_j : j ≠ 0]` on the affine coordinates `T_j / T₀`
(`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`), so sending `Y_j` to `a j` defines a ring
homomorphism `R[T]_{(T₀)} → A`, and that homomorphism is **surjective**: its image is an
`R`-subalgebra containing every `a j`, hence contains the `R`-module they span, which is `A`.

This is the algebraic content of the proof of [Stacks, Tag 0B3I]: the source writes the
surjection as `R[x₁, …, xₙ] → A`, `xᵢ ↦ aᵢ`, and reads it as the statement that
`Spec A → 𝐀ⁿ_S = D₊(T₀) ⊆ 𝐏ⁿ_S` is a closed immersion. Nothing here is geometric; the passage
to schemes is in `StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic`.

## Main definitions

* `Stacks.FiniteMorphismProjective.chartEval`: the evaluation `R[Y_j : j ≠ 0] → A` at the generating
family.
* `Stacks.FiniteMorphismProjective.awayEval`: that evaluation read on `R[T]_{(T₀)}` through the
  chart identification — the ring homomorphism the closed immersion is `Spec` of.

## Main results

* `Stacks.FiniteMorphismProjective.awayEval_surjective`: **the surjection.** It needs only that the
  family spans `A` as an `R`-module; no finiteness of the index and no hypothesis on `R`.
* `Stacks.FiniteMorphismProjective.awayEval_coeffToAway`: on the coefficient ring the homomorphism
  is the structure map of the algebra. This is what makes the resulting closed immersion a morphism
  over the base.
* `Stacks.FiniteMorphismProjective.projZeroRingHom'_comp_algebraMap`: the coefficient ring maps to
  the degree-zero part of the grading by the structure map, so the structure morphism of
  `Proj R[T]` used in this repository is the one the chart identification is stated against.

## References

* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.FiniteMorphismProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)
  (a : {j : Fin (n + 1) // j ≠ 0} → A)

/-! ### The evaluation on the affine coordinates -/

/-- The evaluation `R[Y_j : j ≠ 0] → A` sending the affine coordinate `Y_j` to `a j`. -/
public def chartEval : MvPolynomial {j : Fin (n + 1) // j ≠ 0} R →+* A :=
  MvPolynomial.eval₂Hom (algebraMap R A) a

@[simp] public theorem chartEval_C (r : R) :
    chartEval R A n a (MvPolynomial.C r) = algebraMap R A r :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp] public theorem chartEval_X (j : {j : Fin (n + 1) // j ≠ 0}) :
    chartEval R A n a (MvPolynomial.X j) = a j :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- **The evaluation is surjective as soon as the family spans `A` as an `R`-module.** The image
is a subring containing the image of `R` and every `a j`, hence every `R`-linear combination of
the `a j`. -/
public theorem chartEval_surjective (hgen : Submodule.span R (Set.range a) = ⊤) :
    Function.Surjective (chartEval R A n a) := by
  intro x
  have hx : x ∈ Submodule.span R (Set.range a) := hgen ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨MvPolynomial.X j, chartEval_X R A n a j⟩
  | zero => exact ⟨0, map_zero _⟩
  | add y z _ _ ihy ihz =>
      obtain ⟨p, hp⟩ := ihy
      obtain ⟨q, hq⟩ := ihz
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | smul r y _ ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨MvPolynomial.C r * p, ?_⟩
      rw [map_mul, chartEval_C, hp, Algebra.smul_def]

/-! ### The evaluation on the standard chart -/

/-- **The ring homomorphism `R[T]_{(T₀)} → A`** attached to a family of elements of `A`: the
evaluation on the affine coordinates, read through the identification of the standard chart with
the polynomial ring on them. -/
public def awayEval :
    Away (polyGrading R n) (MvPolynomial.X (0 : Fin (n + 1))) →+* A :=
  (chartEval R A n a).comp (chartEquiv R n 0).symm.toRingHom

/-- **A module-finite algebra is a quotient of the standard affine chart.** -/
public theorem awayEval_surjective (hgen : Submodule.span R (Set.range a) = ⊤) :
    Function.Surjective (awayEval R A n a) :=
  (chartEval_surjective R A n a hgen).comp (chartEquiv R n 0).symm.surjective

/-- **On the coefficient ring the chart homomorphism is the structure map of the algebra.** -/
public theorem awayEval_coeffToAway (r : R) :
    awayEval R A n a (coeffToAway R n 0 r) = algebraMap R A r := by
  have h : (chartEquiv R n 0).symm (coeffToAway R n 0 r) = MvPolynomial.C r := by
    rw [show coeffToAway R n 0 r = chartEquiv R n 0 (MvPolynomial.C r) from
      (chartHom_C R n 0 r).symm]
    exact (chartEquiv R n 0).symm_apply_apply _
  rw [awayEval, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h, chartEval_C]

/-- **The degree-zero part of the grading receives the coefficient ring by its structure map.**
Taking the degree-zero component of a constant polynomial is the identity on it. -/
public theorem projZeroRingHom'_comp_algebraMap :
    (GradedRing.projZeroRingHom' (polyGrading R n)).comp
        (algebraMap R (MvPolynomial (Fin (n + 1)) R)) =
      algebraMap R (polyGrading R n 0) := by
  refine RingHom.ext fun r => ?_
  have hc : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) =
      ((algebraMap R (polyGrading R n 0) r : polyGrading R n 0) :
        MvPolynomial (Fin (n + 1)) R) := by
    rw [SetLike.GradeZero.coe_algebraMap]
    simp [MvPolynomial.algebraMap_eq]
  rw [RingHom.comp_apply, show (algebraMap R (MvPolynomial (Fin (n + 1)) R)) r =
    MvPolynomial.C r from rfl, hc,
    GradedRing.projZeroRingHom'_apply_coe]

end Stacks.FiniteMorphismProjective

end
