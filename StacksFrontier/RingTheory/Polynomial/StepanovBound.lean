module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import StacksFrontier.RingTheory.Polynomial.MonicNormalization
public import StacksFrontier.RingTheory.Polynomial.PlaneCurvePointLowerBound

/-!
# The Weil lower bound for absolutely irreducible plane curves

Let `F` be a finite field with `q` elements and let `f ∈ F[x, y]` be irreducible over an algebraic
closure of `F`, of total degree at most `d`. Then `f` has at least `q - c √q` zeros in `F²`, where
`c` depends only on `d`.

## Main results

* `MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible`: the Weil lower bound for
  absolutely irreducible plane curves.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

universe u

namespace MvPolynomial

open Polynomial.Bivariate

/-- **The Weil lower bound for absolutely irreducible plane curves.** There is `c`, depending
only on `d`, such that over every finite field `F` with `q` elements every `f ∈ F[x, y]` of total
degree at most `d` which is irreducible over an algebraic closure of `F` has at least `q - c √q`
zeros in `F²`. -/
theorem exists_card_zeroSet_ge_of_absolutelyIrreducible (d : ℕ) :
    ∃ c : ℝ, ∀ (F : Type u) [Field F] [Fintype F] (f : MvPolynomial (Fin 2) F),
      f.totalDegree ≤ d → Irreducible (f.map (algebraMap F (AlgebraicClosure F))) →
      (Fintype.card F : ℝ) - c * √(Fintype.card F) ≤
        ({p : Fin 2 → F | MvPolynomial.eval p f = 0}.ncard : ℝ) := by
  choose cm hcm using fun m => Polynomial.Bivariate.exists_card_ge_of_monic.{u} m
  set S : ℝ := ∑ m ∈ Finset.range (d + 1), |cm m|
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => abs_nonneg (cm m)
  refine ⟨S + √(d + 2), fun F _ _ f hfd hirr => ?_⟩
  have hsq := Real.sqrt_nonneg (Fintype.card F : ℝ)
  have hss : √(Fintype.card F : ℝ) * √(Fintype.card F) = Fintype.card F :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rcases le_or_gt (Fintype.card F) (d + 1) with hq | hq
  · have hle : √(Fintype.card F : ℝ) ≤ √(d + 2) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : Fintype.card F ≤ d + 2))
    have : (Fintype.card F : ℝ) ≤ (S + √(d + 2)) * √(Fintype.card F) := by
      nlinarith [mul_le_mul_of_nonneg_right hle hsq]
    exact (sub_nonpos.mpr this).trans (Nat.cast_nonneg _)
  · obtain ⟨g, hmon, -, hnat, hw, hder, hirr', hcard⟩ :=
      exists_monic_normalization f hirr (lt_of_le_of_lt (by omega) hq)
    rw [hnat] at hw
    have h := hcm f.totalDegree F g hmon hnat hw hder hirr'
    rw [← hcard] at h
    have hcS : cm f.totalDegree ≤ S + √(d + 2) :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun m _ => abs_nonneg (cm m))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hfd))).trans
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    nlinarith [mul_le_mul_of_nonneg_right hcS hsq]

end MvPolynomial
