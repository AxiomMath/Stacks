module

public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# A ring with a two-periodic annihilator structure

Let `k` be a commutative ring and let `E = k[X, X⁻¹]/k[X]` be the injective hull of `k` over
`k[X]` in the variable `X`, modelled here as `k[t]` with `X` acting by `t^{n+1} ↦ t^n`,
`1 ↦ 0` (that is, by `Polynomial.divX`). The idealization

`A = k[X] ⋉ E`

is a non-Noetherian ring in which the element `x = X` is a zero-divisor whose annihilators are
periodic: writing `eₙ = t^n ∈ E ⊂ A`,

* `ann(x^{n+1}) = eₙ A`,
* `ann(eₙ) = x^{n+1} A`,
* `x · eₙ₊₁ = eₙ`.

So `A/x^{n+1}` has the two-periodic free resolution `⋯ → A --eₙ--> A --x^{n+1}--> A`, and the
transition maps between successive resolutions are the identity in even degrees. This is the
ring at which the comparison map of [Stacks, Tag 0CQH] fails to be an isomorphism.

## Main definitions

* `Stacks.ShiftIdealization.ShiftModule`: the `k[X]`-module `E`.
* `Stacks.ShiftIdealization.Ring`: the ring `k[X] ⋉ E`.
* `Stacks.ShiftIdealization.x`, `Stacks.ShiftIdealization.e`: the elements `x` and `eₙ`.

## Main results

* `Stacks.ShiftIdealization.x_mul_e_succ`: `x · eₙ₊₁ = eₙ`.
* `Stacks.ShiftIdealization.x_pow_mul_e`: `x^{n+1} eₙ = 0`.
* `Stacks.ShiftIdealization.exists_eq_mul_e_of_x_pow_mul_eq_zero`: `ann(x^{n+1}) ⊆ eₙ A`.
* `Stacks.ShiftIdealization.exists_eq_x_pow_mul_of_e_mul_eq_zero`: `ann(eₙ) ⊆ x^{n+1} A`.
* `Stacks.ShiftIdealization.one_not_mem_span_x`: `x` is not a unit.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.ShiftIdealization

universe u

variable (k : Type u) [CommRing k]

/-- `Polynomial.divX` as a `k`-linear endomorphism of `k[t]`: `t^{n+1} ↦ t^n`, `1 ↦ 0`. -/
def divXLinear : Module.End k k[X] where
  toFun := divX
  map_add' _ _ := divX_add
  map_smul' c p := by
    rw [smul_eq_C_mul, divX_C_mul, ← smul_eq_C_mul]
    rfl

variable {k}

/-- `divXLinear k` acts on a polynomial as `Polynomial.divX`. -/
@[simp]
theorem divXLinear_apply (p : k[X]) : divXLinear k p = divX p := rfl

/-- The iterates of `divX` shift the coefficients down. -/
theorem coeff_divXLinear_pow_apply (j : ℕ) (p : k[X]) (i : ℕ) :
    ((divXLinear k ^ j) p).coeff i = p.coeff (i + j) := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, divXLinear_apply, coeff_divX, ih]
    congr 1
    omega

/-- **The coefficients of `p(divX) m`**: `(p(divX) m)ᵢ = Σ_j pⱼ m_{i + j}`, the sum over any range
past the degree of `p`. -/
theorem coeff_aeval_divXLinear_apply (p m : k[X]) {N : ℕ} (hN : p.natDegree < N) (i : ℕ) :
    ((aeval (divXLinear k) p) m).coeff i =
      ∑ j ∈ Finset.range N, p.coeff j * m.coeff (i + j) := by
  rw [aeval_eq_sum_range' hN, LinearMap.sum_apply, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, coeff_smul, coeff_divXLinear_pow_apply, smul_eq_mul]

/-- **`p(divX) tⁿ` determines the coefficients of `p` up to degree `n`**: its coefficient in
degree `n - i` is the coefficient of `p` in degree `i`. -/
theorem coeff_aeval_divXLinear_X_pow (p : k[X]) (n i : ℕ) (hi : i ≤ n) :
    ((aeval (divXLinear k) p) (X ^ n)).coeff (n - i) = p.coeff i := by
  rw [coeff_aeval_divXLinear_apply p _ (N := max p.natDegree n + 1)
    (Nat.lt_succ_of_le (le_max_left _ _))]
  rw [Finset.sum_eq_single i]
  · rw [coeff_X_pow, ite_eq_left (by omega), mul_one]
  · intro j _ hj
    rw [coeff_X_pow, ite_eq_right (by omega), mul_zero]
  · intro h
    rw [Finset.mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- **Every polynomial of degree at most `n` is `q(divX) tⁿ`**, for `q` the reflection of it. -/
theorem aeval_divXLinear_reflect_X_pow (m : k[X]) {n : ℕ} (hm : m.natDegree ≤ n) :
    (aeval (divXLinear k) (reflect n m)) (X ^ n) = m := by
  have hq : (reflect n m).natDegree < n + 1 :=
    Nat.lt_succ_of_le (natDegree_reflect_le.trans (max_le le_rfl hm))
  ext i
  rw [coeff_aeval_divXLinear_apply _ _ hq]
  by_cases hi : i ≤ n
  · rw [Finset.sum_eq_single (n - i)]
    · rw [coeff_X_pow, ite_eq_left (by omega), mul_one, coeff_reflect, revAt_le (by omega)]
      congr 1
      omega
    · intro j _ hj
      rw [coeff_X_pow, ite_eq_right (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_X_pow, ite_eq_right (by omega), mul_zero]

/-- `divX` undoes multiplication by `X`. -/
theorem divXLinear_pow_X_pow_mul (j : ℕ) (f : k[X]) :
    (divXLinear k ^ j) (X ^ j * f) = f := by
  ext i
  rw [coeff_divXLinear_pow_apply, coeff_X_pow_mul]

variable (k)

/-- The `k[X]`-module `E = k[X, X⁻¹]/k[X]`, modelled as `k[t]` with `X` acting by `divX`. -/
abbrev ShiftModule := Module.AEval' (divXLinear k)

/-- `k[X]` is commutative, so it acts on `E` on the right through the same action. -/
instance : Module (k[X])ᵐᵒᵖ (ShiftModule k) :=
  Module.compHom (ShiftModule k) (RingEquiv.toOpposite k[X]).symm.toRingHom

/-- The left and right actions of `k[X]` on `E` agree. -/
instance : IsCentralScalar k[X] (ShiftModule k) where
  op_smul_eq_smul _ _ := rfl

/-- **The idealization `k[X] ⋉ E`.** -/
abbrev Ring := TrivSqZeroExt k[X] (ShiftModule k)

/-- The element `x = X` of `k[X] ⋉ E`. -/
def x : Ring k := TrivSqZeroExt.inl X

/-- The element `eₙ = tⁿ ∈ E ⊂ k[X] ⋉ E`, which generates the annihilator of `x^{n+1}`. -/
def e (n : ℕ) : Ring k := TrivSqZeroExt.inr (Module.AEval'.of (divXLinear k) (X ^ n))

variable {k}

/-- A polynomial `p` acts on `m ∈ E` as the endomorphism `p(divX)`. -/
theorem smul_of (p m : k[X]) :
    p • Module.AEval'.of (divXLinear k) m =
      Module.AEval'.of (divXLinear k) ((aeval (divXLinear k) p) m) := rfl

/-- `xⁿ` is the image of `Xⁿ` under `k[X] → k[X] ⋉ E`. -/
theorem x_pow (n : ℕ) : x k ^ n = TrivSqZeroExt.inl (X ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, TrivSqZeroExt.inl_one]
  | succ n ih => rw [pow_succ, ih, x, ← TrivSqZeroExt.inl_mul, pow_succ]

/-- `x · eₙ₊₁ = eₙ`. -/
theorem x_mul_e_succ (n : ℕ) : x k * e k (n + 1) = e k n := by
  rw [x, e, e, TrivSqZeroExt.inl_mul_inr, Module.AEval'.X_smul_of]
  congr 2
  rw [divXLinear_apply, divX_X_pow, ite_eq_right (by omega)]
  rfl

/-- `x^{n+1} eₙ = 0`. -/
theorem x_pow_mul_e (n : ℕ) : x k ^ (n + 1) * e k n = 0 := by
  rw [x_pow, e, TrivSqZeroExt.inl_mul_inr, Module.AEval'.X_pow_smul_of]
  rw [show (divXLinear k ^ (n + 1)) • (X ^ n : k[X]) = 0 by
    ext i
    rw [Module.End.smul_def, coeff_divXLinear_pow_apply, coeff_X_pow, ite_eq_right (by omega),
      coeff_zero]]
  simp

/-- **`ann(x^{n+1}) ⊆ eₙ A`.** -/
theorem exists_eq_mul_e_of_x_pow_mul_eq_zero (n : ℕ) {a : Ring k}
    (h : x k ^ (n + 1) * a = 0) : ∃ c : Ring k, a = c * e k n := by
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [x_pow, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_zero] at h1
  rw [x_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_zero, smul_zero, add_zero] at h2
  have hfst : a.fst = 0 := (Polynomial.Monic.mul_right_eq_zero_iff (monic_X_pow (n + 1))).1 h1
  set m : k[X] := (Module.AEval'.of (divXLinear k)).symm a.snd with hm
  have hsnd : a.snd = Module.AEval'.of (divXLinear k) m := by simp [hm]
  rw [hsnd, Module.AEval'.X_pow_smul_of] at h2
  have hdeg : m.natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have := congrArg (fun p : k[X] => p.coeff (i - (n + 1)))
      ((Module.AEval'.of (divXLinear k)).injective (h2.trans (map_zero _).symm))
    simp only [Module.End.smul_def, coeff_divXLinear_pow_apply, coeff_zero] at this
    rwa [show i - (n + 1) + (n + 1) = i by omega] at this
  refine ⟨TrivSqZeroExt.inl (reflect n m), TrivSqZeroExt.ext ?_ ?_⟩
  · rw [hfst, e, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero]
  · rw [e, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.snd_inr, hsnd, smul_of,
      aeval_divXLinear_reflect_X_pow m hdeg]

/-- **`ann(eₙ) ⊆ x^{n+1} A`.** -/
theorem exists_eq_x_pow_mul_of_e_mul_eq_zero (n : ℕ) {a : Ring k}
    (h : e k n * a = 0) : ∃ c : Ring k, a = x k ^ (n + 1) * c := by
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [e, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr, zero_smul, zero_add,
    TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] at h2
  change a.fst • Module.AEval'.of (divXLinear k) (X ^ n) = 0 at h2
  rw [smul_of] at h2
  have h3 : (aeval (divXLinear k) a.fst) (X ^ n) = 0 :=
    (Module.AEval'.of (divXLinear k)).injective (h2.trans (map_zero _).symm)
  have hdvd : X ^ (n + 1) ∣ a.fst := by
    rw [X_pow_dvd_iff]
    intro i hi
    have := coeff_aeval_divXLinear_X_pow a.fst n i (by omega)
    rw [h3, coeff_zero] at this
    exact this.symm
  obtain ⟨q, hq⟩ := hdvd
  set m : k[X] := (Module.AEval'.of (divXLinear k)).symm a.snd with hm
  have hsnd : a.snd = Module.AEval'.of (divXLinear k) m := by simp [hm]
  refine ⟨TrivSqZeroExt.inl q + TrivSqZeroExt.inr
    (Module.AEval'.of (divXLinear k) (X ^ (n + 1) * m)), TrivSqZeroExt.ext ?_ ?_⟩
  · rw [x_pow, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hq]
  · rw [x_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_inl,
      smul_zero, add_zero, Module.AEval'.X_pow_smul_of, hsnd]
    congr 1
    exact (divXLinear_pow_X_pow_mul (n + 1) m).symm

/-- **`x` is not a unit**: `1 ∉ x A`, for `k` non-trivial. -/
theorem one_not_mem_span_x [Nontrivial k] : (1 : Ring k) ∉ Ideal.span {x k} := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  have h1 := congrArg TrivSqZeroExt.fst hc
  rw [TrivSqZeroExt.fst_mul, x, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_one] at h1
  exact not_isUnit_X (IsUnit.of_mul_eq_one (b := TrivSqZeroExt.fst c) (by rw [mul_comm]; exact h1))

end Stacks.ShiftIdealization
