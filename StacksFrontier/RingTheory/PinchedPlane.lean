module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The ring `k + (x, y)²`, the coordinate ring of a pinched plane

For a field `k`, the polynomials in `k[x, y]` without linear terms form a `k`-subalgebra
`R = k + (x, y)²`. It is a domain which is not integrally closed, and `k[x, y]` is integral over
it, with the same fraction field: `x = x³ / x²`. The map `𝔸² ⟶ Spec R` is the normalization of
`Spec R`, a homeomorphism which is an isomorphism away from the maximal ideal `(x, y)²`.

## Main definitions

* `MvPolynomial.noLinearTerms`: the subalgebra `k + (x, y)²` of `k[x, y]`, of the polynomials all
  of whose first partial derivatives vanish at the origin.

## Main results

* `MvPolynomial.X_notMem_noLinearTerms`: the coordinate functions are not in `R`.
* `MvPolynomial.isIntegral_noLinearTerms`: `k[x, y]` is integral over `R`.
* `MvPolynomial.not_isIntegrallyClosed_noLinearTerms`: `R` is not integrally closed.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
-/

@[expose] public noncomputable section

open Polynomial

namespace MvPolynomial

variable (k : Type*) [Field k]

/-- **The subalgebra `k + (x, y)²` of `k[x, y]`**: the polynomials with no linear terms, that is,
whose first partial derivatives all vanish at the origin. -/
def noLinearTerms : Subalgebra k (MvPolynomial (Fin 2) k) where
  carrier := {p | ∀ i, eval 0 (pderiv i p) = 0}
  mul_mem' {p q} hp hq i := by
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp i, hq i]
    ring
  add_mem' {p q} hp hq i := by
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rw [map_add, map_add, hp i, hq i, add_zero]
  algebraMap_mem' a i := by
    simp [MvPolynomial.algebraMap_eq]

variable {k}

/-- A polynomial lies in `k + (x, y)²` if and only if its first partial derivatives all vanish at
the origin. -/
theorem mem_noLinearTerms_iff (p : MvPolynomial (Fin 2) k) :
    p ∈ noLinearTerms k ↔ ∀ i, eval 0 (pderiv i p) = 0 := Iff.rfl

/-- The coordinate functions `x` and `y` are not in `k + (x, y)²`. -/
theorem X_notMem_noLinearTerms (i : Fin 2) : (X i : MvPolynomial (Fin 2) k) ∉ noLinearTerms k := by
  intro h
  have := h i
  simp at this

/-- The powers `X i ^ m` with `m ≥ 2` of the coordinate functions lie in `k + (x, y)²`. -/
theorem X_pow_mem_noLinearTerms (i : Fin 2) {m : ℕ} (hm : 2 ≤ m) :
    (X i : MvPolynomial (Fin 2) k) ^ m ∈ noLinearTerms k := by
  intro j
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast, map_pow, eval_X]
  simp

/-- **`k[x, y]` is integral over `k + (x, y)²`.** -/
theorem isIntegral_noLinearTerms (p : MvPolynomial (Fin 2) k) :
    IsIntegral (noLinearTerms k) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact isIntegral_algebraMap (R := noLinearTerms k)
      (x := ⟨C a, (noLinearTerms k).algebraMap_mem a⟩)
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp =>
    refine hp.mul ⟨Polynomial.X ^ 2 - Polynomial.C ⟨X i ^ 2, X_pow_mem_noLinearTerms i le_rfl⟩,
      monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [Polynomial.eval₂_sub]

/-- **`k + (x, y)²` is not integrally closed.** -/
theorem not_isIntegrallyClosed_noLinearTerms : ¬ IsIntegrallyClosed (noLinearTerms k) := by
  intro hR
  set R := noLinearTerms k
  set K := FractionRing R
  let a : R := ⟨X 0 ^ 3, X_pow_mem_noLinearTerms 0 (by norm_num)⟩
  let b : R := ⟨X 0 ^ 2, X_pow_mem_noLinearTerms 0 le_rfl⟩
  have hb0 : b ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    simp [b] at this
  have hb : b ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hb0
  set x : K := IsLocalization.mk' K a ⟨b, hb⟩
  have hx2 : x ^ 2 = algebraMap R K b := by
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [a, b, SubmonoidClass.mk_pow, MulMemClass.mk_mul_mk]
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (K := K)
    two_pos (hx2 ▸ isIntegral_algebraMap)
  have hyb : y * b = a := by
    apply IsFractionRing.injective R K
    rw [map_mul, hy, IsLocalization.mk'_spec]
  have hyX : (y : MvPolynomial (Fin 2) k) = X 0 := by
    have h := congrArg Subtype.val hyb
    simp only [MulMemClass.coe_mul, a, b] at h
    have hX : (X 0 : MvPolynomial (Fin 2) k) ^ 2 ≠ 0 := pow_ne_zero _ (X_ne_zero 0)
    refine mul_right_cancel₀ hX ?_
    rw [h]
    ring
  exact X_notMem_noLinearTerms 0 (hyX ▸ y.2)

end MvPolynomial

end
