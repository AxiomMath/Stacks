module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.CuspForm

/-!
# The Hecke polynomial

Basic properties of `Stacks.Adeles.heckePolynomial m q t`
`= ∑_{i=0}^{m} (-1)^i q^{i(i-1)/2} t_i X^{m-i}` (with `t_0 = 1`): it is monic of degree `m`, its
coefficient of `X^{m-i}` is `(-1)^i q^{i(i-1)/2} t_i`, and it is compatible with ring maps.
-/

@[expose] public noncomputable section

open Polynomial

universe w

namespace Stacks.Adeles

variable {Λ : Type w} [CommRing Λ] (m q : ℕ) (t : ℕ → Λ)

/-- The coefficient of the Hecke polynomial in front of `X^{m-i}`, `i ≤ m`. -/
public theorem coeff_heckePolynomial_sub {i : ℕ} (hi : i ≤ m) :
    (heckePolynomial m q t).coeff (m - i) =
      (-1) ^ i * (q : Λ) ^ (i * (i - 1) / 2) * (if i = 0 then 1 else t i) := by
  rw [heckePolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp only [coeff_C_mul_X_pow, ↓reduceIte]
  · intro j hj hji
    have := Finset.mem_range.1 hj
    have hne : ¬m - i = m - j := by omega
    simp only [coeff_C_mul_X_pow, hne, ↓reduceIte]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- The Hecke polynomial is `X^m` plus terms of lower degree. -/
public theorem heckePolynomial_eq_X_pow_add :
    heckePolynomial m q t = X ^ m + ∑ i ∈ Finset.range m,
      C ((-1) ^ (i + 1) * (q : Λ) ^ ((i + 1) * (i + 1 - 1) / 2) * t (i + 1)) *
        X ^ (m - (i + 1)) := by
  rw [heckePolynomial, Finset.sum_range_succ', add_comm]
  congr 1
  · simp

/-- The lower terms of the Hecke polynomial have degree `< m`. -/
theorem degree_heckePolynomial_tail_lt [Nontrivial Λ] :
    (∑ i ∈ Finset.range m,
      C ((-1) ^ (i + 1) * (q : Λ) ^ ((i + 1) * (i + 1 - 1) / 2) * t (i + 1)) *
        X ^ (m - (i + 1))).degree < (X ^ m : Λ[X]).degree := by
  rw [degree_X_pow]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  have := Finset.mem_range.1 hi
  exact_mod_cast (show m - (i + 1) < m by omega)

/-- The Hecke polynomial is monic. -/
public theorem monic_heckePolynomial [Nontrivial Λ] : (heckePolynomial m q t).Monic := by
  rw [heckePolynomial_eq_X_pow_add]
  exact (monic_X_pow m).add_of_left (degree_heckePolynomial_tail_lt m q t)

/-- The Hecke polynomial has degree `m`. -/
public theorem natDegree_heckePolynomial [Nontrivial Λ] :
    (heckePolynomial m q t).natDegree = m := by
  rw [heckePolynomial_eq_X_pow_add, natDegree_add_eq_left_of_degree_lt
    (degree_heckePolynomial_tail_lt m q t), natDegree_X_pow]

/-- The Hecke polynomial is compatible with ring maps. -/
public theorem map_heckePolynomial {Λ' : Type*} [CommRing Λ'] (φ : Λ →+* Λ') :
    (heckePolynomial m q t).map φ = heckePolynomial m q (fun i => φ (t i)) := by
  simp only [heckePolynomial, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    map_C, map_X, map_mul, map_pow, map_neg, map_one, map_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Stacks.Adeles

end
