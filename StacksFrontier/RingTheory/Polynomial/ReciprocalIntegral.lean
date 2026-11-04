module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Reciprocal roots of an integral polynomial are algebraic integers

Let `P` be a polynomial with integer coefficients, of degree at most `N`, with constant
coefficient `1`, and suppose its image in a commutative ring `Ω` factors as a product of `N`
linear factors `∏_{i} (1 - α_i T)`.  Then every `α_i` is an algebraic integer.

The polynomial witnessing this is the reflection `reflect N P`, whose coefficient of `T ^ j` is
the coefficient of `T ^ (N - j)` of `P`.  It is monic of degree `N` because the constant
coefficient of `P` is `1`, and its image in `Ω` is `∏_i (T - α_i)` because reflecting a product
of linear factors reverses each factor: `reflect 1 (1 - a T) = T - a`.  Evaluating at `α_i`
kills the `i`-th factor.

This is the step by which the eigenvalues of geometric Frobenius on the first cohomology of a
curve over a finite field are seen to be algebraic integers: what the geometry provides is the
integrality of the *numerator of the zeta function*, a polynomial whose reciprocal roots are
the eigenvalues.

## Main results

* `Polynomial.reflect_finsetProd`: reflecting a finite product of polynomials, at the sum of
  degree bounds for the factors, is the product of the reflections.
* `Polynomial.reflect_one_sub_C_mul_X`: `reflect 1 (1 - a T) = T - a`.
* `exists_monic_map_eq_prod_X_sub_C`: the reversed factorization `∏_i (T - α_i)` is the image
  of a monic integral polynomial.
* `isIntegral_of_prod_one_sub_C_mul_X_eq_map`: the statement above.
-/

@[expose] public noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Reflecting at an index beyond the degree bound leaves it alone. -/
public theorem revAt_of_lt {N m : ℕ} (h : N < m) : revAt N m = m :=
  revAt_eq_self_of_lt h

/-- A linear polynomial `1 - a T` has degree at most one. -/
public theorem natDegree_one_sub_C_mul_X_le (a : R) : (1 - C a * X).natDegree ≤ 1 := by
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · simp
  · exact le_trans natDegree_mul_le (by simpa using natDegree_X_le)

/-- Reflecting `1 - a T` at degree one reverses it to `T - a`. -/
public theorem reflect_one_sub_C_mul_X (a : R) : reflect 1 (1 - C a * X) = X - C a := by
  ext n
  rw [coeff_reflect]
  match n with
  | 0 => simp [revAt_le (Nat.zero_le 1), coeff_one, coeff_C, coeff_X]
  | 1 => simp [revAt_le (le_refl 1), coeff_one, coeff_C, coeff_X]
  | (m + 2) =>
      rw [revAt_of_lt (by omega)]
      simp [coeff_X, coeff_one]

/-- Reflecting a finite product, at the sum of degree bounds for the factors, is the product of
the reflections of the factors. -/
public theorem reflect_finsetProd {ι : Type*} (s : Finset ι) (f : ι → R[X]) (D : ι → ℕ)
    (hD : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    reflect (∑ i ∈ s, D i) (∏ i ∈ s, f i) = ∏ i ∈ s, reflect (D i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hprod : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, D j :=
        le_trans (natDegree_prod_le _ _)
          (Finset.sum_le_sum fun j hj => hD j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
        reflect_mul _ _ (hD i (Finset.mem_insert_self i s)) hprod,
        ih fun j hj => hD j (Finset.mem_insert_of_mem hj)]

end Polynomial

open Polynomial

/-- Reversing a factorization into reciprocal linear factors.  If a polynomial `P` over `ℤ` of
degree at most `N = #ι` has constant coefficient `1` and its image in a commutative ring `Ω` is
`∏_{i : ι} (1 - α_i T)`, then `∏_{i} (T - α_i)` is the image of a monic integral polynomial,
namely of `reflect N P`. -/
public theorem exists_monic_map_eq_prod_X_sub_C {Ω : Type*} [CommRing Ω] {ι : Type*}
    [Fintype ι] (α : ι → Ω) {P : ℤ[X]} (hdeg : P.natDegree ≤ Fintype.card ι)
    (h0 : P.coeff 0 = 1)
    (hP : P.map (Int.castRingHom Ω) = ∏ i, (1 - C (α i) * X)) :
    ∃ Q : ℤ[X], Q.Monic ∧ Q.map (Int.castRingHom Ω) = ∏ i, (X - C (α i)) := by
  classical
  set N := Fintype.card ι with hN
  have hcoeffN : (reflect N P).coeff N = 1 := by
    rw [coeff_reflect, revAt_le (le_refl N), Nat.sub_self, h0]
  have hle : (reflect N P).natDegree ≤ N := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    rw [coeff_reflect, revAt_of_lt hm]
    exact natDegree_le_iff_coeff_eq_zero.1 hdeg m hm
  have hdegeq : (reflect N P).natDegree = N :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeffN]; exact one_ne_zero))
  have hmonic : (reflect N P).Monic := by
    rw [Monic, leadingCoeff, hdegeq, hcoeffN]
  refine ⟨reflect N P, hmonic, ?_⟩
  have hcomm : (reflect N P).map (Int.castRingHom Ω)
      = reflect N (P.map (Int.castRingHom Ω)) := by
    ext n
    simp [coeff_reflect]
  rw [hcomm, hP, show N = ∑ _j : ι, 1 by simp [hN],
    reflect_finsetProd _ _ _ fun j _ => natDegree_one_sub_C_mul_X_le (α j)]
  exact Finset.prod_congr rfl fun j _ => reflect_one_sub_C_mul_X (α j)

/-- **Reciprocal roots of an integral polynomial are algebraic integers.**  If a polynomial `P`
over `ℤ` of degree at most `N = #ι` has constant coefficient `1` and its image in a commutative
ring `Ω` is `∏_{i : ι} (1 - α_i T)`, then every `α_i` is an algebraic integer. -/
public theorem isIntegral_of_prod_one_sub_C_mul_X_eq_map {Ω : Type*} [CommRing Ω] {ι : Type*}
    [Fintype ι] (α : ι → Ω) {P : ℤ[X]} (hdeg : P.natDegree ≤ Fintype.card ι)
    (h0 : P.coeff 0 = 1)
    (hP : P.map (Int.castRingHom Ω) = ∏ i, (1 - C (α i) * X)) (i : ι) :
    IsIntegral ℤ (α i) := by
  obtain ⟨Q, hmonic, hmap⟩ := exists_monic_map_eq_prod_X_sub_C α hdeg h0 hP
  refine ⟨Q, hmonic, ?_⟩
  have hzero : eval (α i) (Q.map (Int.castRingHom Ω)) = 0 := by
    rw [hmap, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [eval₂_eq_eval_map, RingHom.ext_int (algebraMap ℤ Ω) (Int.castRingHom Ω)]
  exact hzero

end
