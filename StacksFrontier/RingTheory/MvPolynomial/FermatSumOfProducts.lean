module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The Fermat polynomial is not a short sum of products

Over a finite field, a finite family of polynomials without constant term whose total degrees sum
to less than the number of variables has a common zero other than the origin: the origin is a
common zero, and Chevalley–Warning makes the number of common zeros divisible by the
characteristic.

Differentiating a decomposition `∑ⱼ Xⱼ ^ d = ∑ᵢ uᵢ vᵢ` with `uᵢ, vᵢ` without constant term and
evaluating at such a common zero `x` leaves `d * xⱼ ^ (d - 1) = 0` for every `j`, because every
term of the derivative of the right hand side retains a factor `uᵢ` or `vᵢ`. For `d` prime to the
characteristic this forces `x = 0`, so no such decomposition exists.

## Main results

* `MvPolynomial.exists_ne_zero_forall_eval_eq_zero`: a family of polynomials without constant
  term over a finite field, of total degrees summing to less than the number of variables, has a
  nonzero common zero.
* `MvPolynomial.sum_X_pow_ne_sum_mul`: the Fermat polynomial `∑ⱼ Xⱼ ^ d` of degree `d` prime to
  the characteristic is not a sum `∑ᵢ uᵢ vᵢ` of products of polynomials without constant term
  whose total degrees sum to less than the number of variables.
-/

@[expose] public section

namespace MvPolynomial

variable {K : Type*} [Field K] [Finite K] {ι : Type*} {n : ℕ}

/-- A finite family of polynomials without constant term in `n` variables over a finite field,
whose total degrees sum to less than `n`, has a common zero other than the origin. -/
theorem exists_ne_zero_forall_eval_eq_zero {s : Finset ι} (f : ι → MvPolynomial (Fin n) K)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0)
    (hdeg : ∑ i ∈ s, (f i).totalDegree < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i ∈ s, eval x (f i) = 0 := by
  have := Fintype.ofFinite K
  have : DecidableEq K := Classical.decEq K
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  have hdeg' : ∑ i ∈ s, (f i).totalDegree < Fintype.card (Fin n) := by rwa [Fintype.card_fin]
  have hdvd := char_dvd_card_solutions_of_sum_lt (K := K) (σ := Fin n) (ι := ι)
    (s := s) (f := f) (ringChar K) hdeg'
  have hzero : ∀ i ∈ s, eval (0 : Fin n → K) (f i) = 0 := by
    intro i hi
    rw [eval_zero]
    exact hf i hi
  have hpos : 0 < Fintype.card { x : Fin n → K // ∀ i ∈ s, eval x (f i) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hne : Fintype.card { x : Fin n → K // ∀ i ∈ s, eval x (f i) = 0 } ≠ 1 := by
    intro h
    rw [h] at hdvd
    exact (Fact.out : (ringChar K).Prime).one_lt.ne' (Nat.dvd_one.mp hdvd)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (⟨0, hzero⟩ :
    { x : Fin n → K // ∀ i ∈ s, eval x (f i) = 0 })
  exact ⟨y.val, fun h => hy (Subtype.ext h), y.property⟩

/-- Over a finite field the Fermat polynomial `∑ⱼ Xⱼ ^ d` in `n` variables, with `d` prime to the
characteristic, is not a sum `∑ᵢ uᵢ vᵢ` of products of polynomials without constant term whose
total degrees sum to less than `n`. -/
theorem sum_X_pow_ne_sum_mul {d : ℕ} {s : Finset ι} (u v : ι → MvPolynomial (Fin n) K)
    (hd : (d : K) ≠ 0) (hd2 : 2 ≤ d)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) (hv : ∀ i ∈ s, constantCoeff (v i) = 0)
    (hdeg : ∑ i ∈ s, ((u i).totalDegree + (v i).totalDegree) < n) :
    ∑ j : Fin n, (X j : MvPolynomial (Fin n) K) ^ d ≠ ∑ i ∈ s, u i * v i := by
  classical
  intro heq
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_forall_eval_eq_zero
      (s := s ×ˢ (Finset.univ : Finset Bool))
      (f := fun ib => if ib.2 then u ib.1 else v ib.1)
      (by
        rintro ⟨i, b⟩ hib
        rw [Finset.mem_product] at hib
        cases b <;> simp [hu i hib.1, hv i hib.1])
      (by
        rw [Finset.sum_product]
        refine lt_of_le_of_lt (le_of_eq (Finset.sum_congr rfl ?_)) hdeg
        intro i _
        rw [Fintype.sum_bool]
        simp)
  have hxu : ∀ i ∈ s, eval x (u i) = 0 := fun i hi => hx (i, true) (by simp [hi])
  have hxv : ∀ i ∈ s, eval x (v i) = 0 := fun i hi => hx (i, false) (by simp [hi])
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx0 (funext fun j => by simpa using not_not.mp (not_exists.mp h j))
  have hL : pderiv j (∑ j' : Fin n, (X j' : MvPolynomial (Fin n) K) ^ d) =
      (d : MvPolynomial (Fin n) K) * X j ^ (d - 1) := by
    rw [map_sum, Finset.sum_eq_single j]
    · rw [pderiv_pow, pderiv_X_self, mul_one]
    · intro b _ hb
      rw [pderiv_pow, pderiv_X_of_ne hb, mul_zero]
    · simp
  have hR : eval x (pderiv j (∑ i ∈ s, u i * v i)) = 0 := by
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [pderiv_mul, map_add, map_mul, map_mul, hxu i hi, hxv i hi, zero_mul, mul_zero, add_zero]
  have hcalc : (d : K) * x j ^ (d - 1) = 0 := by
    have := congrArg (fun P => eval x (pderiv j P)) heq
    simp only [hL, hR, map_mul, map_pow, eval_X, map_natCast] at this
    exact this
  rcases mul_eq_zero.mp hcalc with h | h
  · exact hd h
  · exact hj ((pow_eq_zero_iff (show d - 1 ≠ 0 by omega)).mp h)

end MvPolynomial

end
