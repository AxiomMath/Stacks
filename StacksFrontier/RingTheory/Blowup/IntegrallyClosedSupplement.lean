module

public import StacksFrontier.RingTheory.Blowup.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.Blowup.Basic

/-!
# Elements integral over an ideal

An element `x` of a ring `R` is integral over an ideal `I` when it satisfies a monic equation
whose coefficient in degree `j` lies in `I ^ (k - j)`, `k` the degree.

## Main definitions

* `Ideal.IsIntegralOver`: `x` is integral over the ideal `I`.

## Main results

* `Ideal.isIntegralOver_of_mem`: every element of `I` is integral over `I`.
* `Ideal.IsIntegralOver.exists_pow_mem`: an element integral over `I` has a positive power in `I`.
* `Ideal.IsIntegralOver.isIntegral_affineBlowup`: if `x` is integral over `I ^ n`, then `x / aⁿ`
  is integral over the affine blowup algebra `R[I/a]`.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **An element integral over an ideal.** `x` is integral over `I` when it satisfies a monic
equation of positive degree `k` whose coefficient in degree `j` lies in `I ^ (k - j)`. For
`I = ⊤` this is ordinary integrality over `R`, which every element satisfies. -/
def IsIntegralOver (I : Ideal R) (x : R) : Prop :=
  ∃ (k : ℕ) (c : ℕ → R), 0 < k ∧ (∀ j < k, c j ∈ I ^ (k - j)) ∧
    x ^ k + ∑ j ∈ Finset.range k, c j * x ^ j = 0

/-- Every element of an ideal is integral over it. -/
theorem isIntegralOver_of_mem {I : Ideal R} {x : R} (hx : x ∈ I) : I.IsIntegralOver x := by
  refine ⟨1, fun _ => -x, Nat.one_pos, fun j hj => ?_, by simp⟩
  obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
  simpa using neg_mem hx

/-- **An element integral over `I` has a positive power in `I`.** -/
theorem IsIntegralOver.exists_pow_mem {I : Ideal R} {x : R} (hx : I.IsIntegralOver x) :
    ∃ k, 0 < k ∧ x ^ k ∈ I := by
  obtain ⟨k, c, hk, hc, hrel⟩ := hx
  refine ⟨k, hk, ?_⟩
  have hxk : x ^ k = -∑ j ∈ Finset.range k, c j * x ^ j := eq_neg_of_add_eq_zero_left hrel
  rw [hxk]
  refine neg_mem (Submodule.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_)
  have hjk : j < k := Finset.mem_range.mp hj
  exact Ideal.pow_le_self (by lia) (hc j hjk)

end Ideal

section Chart

variable {R : Type*} [CommRing R] (I : Ideal R) (a : R)

/-- **An element integral over `Iⁿ` is integral over the chart `R[I/a]` after division by
`aⁿ`.** -/
theorem Ideal.IsIntegralOver.isIntegral_affineBlowup {n : ℕ} {x : R}
    (hx : (I ^ n).IsIntegralOver x) :
    IsIntegral ↥(affineBlowup I a)
      (Localization.mk x ⟨a ^ n, n, rfl⟩ : Localization.Away a) := by
  classical
  obtain ⟨k, c, hk, hc, hrel⟩ := hx
  set S := Localization.Away a
  set t : S := algebraMap R S a
  set y : S := Localization.mk x ⟨a ^ n, n, rfl⟩
  have hcmem : ∀ j : ℕ, j < k →
      (Localization.mk (c j) ⟨a ^ (n * (k - j)), n * (k - j), rfl⟩ : S)
        ∈ affineBlowup I a := by
    refine fun j hj => mk_mem_affineBlowup_of_mem_pow I a ?_
    rw [pow_mul]
    exact hc j hj
  set γ : ℕ → ↥(affineBlowup I a) := fun j =>
    if hj : j < k then ⟨_, hcmem j hj⟩ else 0 with hγdef
  have hγcoe : ∀ j ∈ Finset.range k,
      (γ j : S) * t ^ (n * (k - j)) = algebraMap R S (c j) := by
    intro j hj
    rw [hγdef]
    simp only [dite_eq_left (Finset.mem_range.mp hj)]
    exact mk_pow_mul_algebraMap_pow_eq a (n * (k - j)) (c j)
  have hX : (algebraMap R S x) ^ k
      + ∑ j ∈ Finset.range k, algebraMap R S (c j) * (algebraMap R S x) ^ j = 0 := by
    simpa only [map_add, map_pow, map_sum, map_mul, map_zero]
      using congrArg (algebraMap R S) hrel
  have hzero := mul_pow_eq_zero_of_monic_relation
    (mk_pow_mul_algebraMap_pow_eq a n x) hγcoe hX
  have hunit : IsUnit (t ^ (n * k)) :=
    (IsLocalization.map_units S (⟨a, 1, pow_one a⟩ : Submonoid.powers a)).pow _
  have hrelS : y ^ k + ∑ j ∈ Finset.range k, (γ j : S) * y ^ j = 0 :=
    (hunit.mul_left_eq_zero).mp hzero
  refine ⟨Polynomial.X ^ k + ∑ j ∈ Finset.range k, Polynomial.C (γ j) * Polynomial.X ^ j,
    Polynomial.monic_X_pow_add ?_, ?_⟩
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_)
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j (γ j))
      (by exact_mod_cast Finset.mem_range.mp hj)
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    exact hrelS

end Chart

end
