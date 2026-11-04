module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumPolynomials
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterization of the power-sum polynomials

The universal power-sum polynomial is characterized among weighted-homogeneous integral
polynomials by its values on the elementary symmetric polynomials in every sufficiently large
finite set of variables.

## Main results

* `AlgebraicGeometry.eq_powerSumPolynomial_iff_eval_esymm` gives the evaluation property and
  its uniqueness characterization.

## Implementation notes

The variables of the universal polynomial are indexed by positive natural numbers.
Substitution sends the variable indexed by `i` to the `i`th elementary symmetric polynomial in
`n` variables. Packaging a candidate in the weighted-homogeneous submodule expresses the
homogeneity assumption in the source. The right side uses Mathlib's `MvPolynomial.psum` for
the sum of the `p`th powers.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

/-- The variable index of the `i`-th Chern class, for `i` ranging over the first `p` positive
integers. -/
private def index (p : ℕ) (i : Fin p) : ℕ+ := ⟨i.1 + 1, by omega⟩

/-- A weighted-homogeneous polynomial of degree `p` involves only the variables of weight at
most `p`, so only the indices in the range of `index p`. -/
private theorem vars_subset_index {p : ℕ}
    (Q : weightedHomogeneousSubmodule ℤ (fun i : ℕ+ => (i : ℕ)) p) :
    ↑(Q : MvPolynomial ℕ+ ℤ).vars ⊆ Set.range (index p) := by
  intro i hi
  rcases (MvPolynomial.mem_vars_iff_mem_support i).mp hi with ⟨d, hd, hdi⟩
  have hle : (i : ℕ) ≤ p :=
    (Finsupp.le_weight_of_ne_zero' (fun j : ℕ+ => (j : ℕ))
      (Finsupp.mem_support_iff.mp hdi)).trans_eq
      (Q.property (MvPolynomial.mem_support_iff.mp hd))
  have hipos := i.pos
  exact ⟨⟨i - 1, by omega⟩, PNat.eq (by change (i : ℕ) - 1 + 1 = (i : ℕ); omega)⟩

/-- Distinct indices give distinct variables. -/
private theorem index_injective (p : ℕ) : Function.Injective (index p) := fun _ _ h =>
  Fin.ext (by simpa [index] using congrArg (fun x : ℕ+ => (x : ℕ)) h)

/-- Substituting the elementary symmetric polynomials in `p` variables is injective on
polynomials whose variables are among the first `p` Chern-class variables; this is the
fundamental theorem of symmetric polynomials. -/
private theorem eval_esymm_injective (p : ℕ)
    {Q R : MvPolynomial ℕ+ ℤ}
    (hQ : ↑Q.vars ⊆ Set.range (index p))
    (hR : ↑R.vars ⊆ Set.range (index p))
    (he : eval₂Hom C (fun i : ℕ+ => esymm (Fin p) ℤ (i : ℕ)) Q =
      eval₂Hom C (fun i : ℕ+ => esymm (Fin p) ℤ (i : ℕ)) R) : Q = R := by
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q (index p)
    (index_injective p) hQ
  obtain ⟨r, hr⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range R (index p)
    (index_injective p) hR
  have he' : (esymmAlgHom (Fin p) ℤ p q).val =
      (esymmAlgHom (Fin p) ℤ p r).val := by
    rw [esymmAlgHom_apply, esymmAlgHom_apply]
    rw [← hq, ← hr] at he
    simpa [MvPolynomial.eval₂Hom_rename, index, MvPolynomial.aeval_def,
      Function.comp_def] using he
  rw [← hq, ← hr]
  exact congrArg (rename (index p)) (esymmAlgHom_fin_injective ℤ (le_refl p)
    (show esymmAlgHom (Fin p) ℤ p q = esymmAlgHom (Fin p) ℤ p r from Subtype.ext he'))

/-- Substituting the elementary symmetric polynomials in `n ≥ k` variables into the power-sum
polynomial of positive degree `k` gives the sum of the `k`th powers. -/
private theorem eval₂Hom_esymm_fin_powerSumPolynomial :
    ∀ k : ℕ, 0 < k → ∀ n : ℕ, k ≤ n →
      eval₂Hom C (fun i : ℕ+ => esymm (Fin n) ℤ (i : ℕ))
          (powerSumPolynomial k : MvPolynomial ℕ+ ℤ) = psum (Fin n) ℤ k := by
  classical
  intro k
  induction k using Nat.case_strong_induction_on with
  | hz => intro hk; omega
  | hi k ih =>
      intro hk n hn
      rw [coe_powerSumPolynomial_succ, map_add, map_sum]
      simp only [map_mul, eval₂Hom_C, eval₂Hom_X', map_pow]
      rw [psum_eq_mul_esymm_sub_sum (Fin n) ℤ (k + 1) (by omega)]
      have hsum : (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 ∈ Set.Ioo 0 (k + 1),
          (-1 : MvPolynomial (Fin n) ℤ) ^ a.1 * esymm (Fin n) ℤ a.1 *
            psum (Fin n) ℤ a.2) =
          ∑ j ∈ Finset.range k, (-1 : MvPolynomial (Fin n) ℤ) ^ (j + 1) *
            esymm (Fin n) ℤ (j + 1) * psum (Fin n) ℤ (k - j) := by
        rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_succ]
        simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Set.mem_Ioo,
          lt_irrefl, false_and, ite_false, zero_add]
        rw [Finset.sum_range_succ]
        simp only [lt_irrefl, and_false, ite_false, add_zero]
        exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
      rw [hsum, eq_sub_iff_add_eq, add_right_comm, ← Finset.sum_add_distrib,
        Finset.sum_eq_zero fun j hj => ?_, zero_add,
        show (Nat.succPNat k : ℕ) = k + 1 by rfl]
      · simp only [map_neg, map_one, map_add, map_natCast]
        push_cast
        ring
      · have hjk : j < k := Finset.mem_range.mp hj
        rw [ih (k - j) (by omega) (by omega) n (by omega),
          show (Nat.succPNat j : ℕ) = j + 1 by rfl]
        simp only [map_neg, map_one]
        ring

/-- A weighted-homogeneous integral polynomial of positive degree `p` is the universal
power-sum polynomial precisely when substituting elementary symmetric polynomials in any
`n ≥ p` variables gives the sum of their `p`th powers. -/
@[stacks 0F9B "power_sum_characterization"]
public theorem eq_powerSumPolynomial_iff_eval_esymm
    (p : ℕ) (hp : 1 ≤ p)
    (Q : weightedHomogeneousSubmodule ℤ (fun i : ℕ+ => (i : ℕ)) p) :
    Q = powerSumPolynomial p ↔
      ∀ n : ℕ, p ≤ n →
        eval₂Hom C (fun i : ℕ+ => esymm (Fin n) ℤ (i : ℕ))
            (Q : MvPolynomial ℕ+ ℤ) =
          psum (Fin n) ℤ p := by
  refine ⟨?_, fun hQ => Subtype.ext <| eval_esymm_injective p (vars_subset_index Q)
    (vars_subset_index (powerSumPolynomial p))
    ((hQ p le_rfl).trans (eval₂Hom_esymm_fin_powerSumPolynomial p hp p le_rfl).symm)⟩
  rintro rfl n hn
  exact eval₂Hom_esymm_fin_powerSumPolynomial p hp n hn

end AlgebraicGeometry
