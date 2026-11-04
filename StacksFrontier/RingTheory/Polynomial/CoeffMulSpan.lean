module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The coefficients of a product of polynomials with a unit coefficient generate the unit ideal

Let `P` and `Q` be polynomials over a commutative ring `R`, of degrees at most `n` and `m`, each
having some coefficient equal to `1`. Then the `n + m + 1` coefficients of `P * Q` generate the
unit ideal of `R`.

## Main results

* `Polynomial.span_range_coeff_mul_eq_top`: the coefficients of `P * Q` generate the unit ideal
  when `P` and `Q` each have a coefficient equal to `1`.
* `Polynomial.map_ofFn`: `Polynomial.ofFn` commutes with ring homomorphisms.
-/

@[expose] public noncomputable section

namespace Polynomial

/-- `Polynomial.ofFn` commutes with ring homomorphisms. -/
theorem map_ofFn {R S : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq R] [DecidableEq S]
    (φ : R →+* S) {n : ℕ} (v : Fin n → R) :
    (ofFn n v).map φ = ofFn n (fun i => φ (v i)) := by
  ext k
  rw [coeff_map]
  by_cases hk : k < n
  · rw [ofFn_coeff_eq_val_of_lt _ hk, ofFn_coeff_eq_val_of_lt _ hk]
  · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.1 hk), ofFn_coeff_eq_zero_of_ge _ (not_lt.1 hk),
      map_zero]

/-- **The coefficients of a product of two polynomials, each with a coefficient equal to `1`,
generate the unit ideal.** If `P` and `Q` have degrees at most `n` and `m` and some coefficient
of each is `1`, the `n + m + 1` coefficients of `P * Q` span the unit ideal. -/
theorem span_range_coeff_mul_eq_top {R : Type*} [CommRing R] {n m : ℕ} {P Q : R[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ m) {a b : ℕ} (ha : P.coeff a = 1)
    (hb : Q.coeff b = 1) :
    Ideal.span (Set.range fun k : Fin (n + m + 1) => (P * Q).coeff k) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  let := Ideal.Quotient.field M
  have hP0 : P.map (Ideal.Quotient.mk M) ≠ 0 := fun h0 => by
    simpa [ha] using congrArg (coeff · a) h0
  have hQ0 : Q.map (Ideal.Quotient.mk M) ≠ 0 := fun h0 => by
    simpa [hb] using congrArg (coeff · b) h0
  have hkle : ((P * Q).map (Ideal.Quotient.mk M)).natDegree < n + m + 1 :=
    Nat.lt_succ_of_le (natDegree_map_le.trans (natDegree_mul_le.trans (add_le_add hP hQ)))
  refine leadingCoeff_ne_zero.2 ((Polynomial.map_mul _).trans_ne (mul_ne_zero hP0 hQ0)) ?_
  rw [leadingCoeff, coeff_map]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨⟨_, hkle⟩, rfl⟩))

end Polynomial

end
