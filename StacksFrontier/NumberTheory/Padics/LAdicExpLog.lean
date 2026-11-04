module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The `ℓ`-adic logarithm and exponential in a Banach algebra

Let `𝔸` be a complete ultrametric normed algebra over `ℚ_ℓ` (for instance `M_r(ℚ_ℓ)` with the
sup norm, or the bounded operators on an ultrametric Banach space).  This file builds the
logarithm on the disc `‖u - 1‖ ≤ ℓ⁻¹` as the limit

`log u = lim_{m → ∞} ℓ^{-m} (u^{ℓ^m} - 1)`,

and relates it to the exponential series `NormedSpace.exp`, which converges on `‖x‖ < ℓ⁻¹`.
The limit definition makes the group-theoretic properties immediate: the logarithm of a product
of commuting elements is the sum of the logarithms, it commutes with continuous algebra maps,
and it lies in every closed subalgebra containing `u`.  The two inverse relations follow from
`log (exp x) = x`, which is read off from the limit, and the injectivity of the logarithm on the
open disc `‖u - 1‖ < ℓ⁻¹`, which comes from the estimate `‖log u - (u - 1)‖ ≤ ℓ ‖u - 1‖²`.

This is the analytic input of the `ℓ`-adic Lie-algebra argument for Deligne's finiteness of the
outer action of Frobenius on the geometric monodromy (Weil II, 1.3.9): Mathlib's convergence
results for the exponential are stated over `ℝ` and `ℂ` only.

## Main definitions

* `Stacks.LAdic.ladicLog`: the `ℓ`-adic logarithm.

## Main results

* `Stacks.LAdic.tendsto_logSeq`: on `‖u - 1‖ ≤ ℓ⁻¹` the approximations converge to `log u`.
* `Stacks.LAdic.norm_ladicLog_sub_le`: `‖log u - (u - 1)‖ ≤ ℓ ‖u - 1‖²`.
* `Stacks.LAdic.ladicLog_mul_of_commute`, `Stacks.LAdic.ladicLog_pow`, `Stacks.LAdic.map_ladicLog`,
  `Stacks.LAdic.ladicLog_mem`.
* `Stacks.LAdic.eq_one_of_ladicLog_eq_zero`: the logarithm has no kernel on `‖u - 1‖ < ℓ⁻¹`.

## References

* J.-P. Serre, *Lie algebras and Lie groups*, Part II, Chapter V.
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.
-/

@[expose] public noncomputable section

open Filter Topology

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ_[ℓ] 𝔸] [IsUltrametricDist 𝔸]

/-- In an ultrametric normed ring, `‖a + b‖ ≤ r` if `‖a‖ ≤ r` and `‖b‖ ≤ r`. -/
private theorem norm_add_le_of_le_of_le {a b : 𝔸} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) :
    ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

omit [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] 𝔸] in
/-- In an ultrametric normed ring, `‖n • x‖ ≤ ‖x‖`. -/
theorem norm_nsmul_le_of_ultrametric (n : ℕ) (x : 𝔸) : ‖n • x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact norm_add_le_of_le_of_le ih le_rfl

omit [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] 𝔸] in
/-- The binomial estimate `‖(1 + a) ^ n - 1 - n a‖ ≤ ‖a‖²` for `‖a‖ ≤ 1`. -/
theorem norm_one_add_pow_sub_le {a : 𝔸} (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖(1 + a) ^ n - 1 - n • a‖ ≤ ‖a‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : (1 + a) ^ (n + 1) - 1 - (n + 1) • a =
        ((1 + a) ^ n - 1 - n • a) + ((1 + a) ^ n - 1 - n • a) * a + n • (a * a) := by
      rw [pow_succ]
      generalize (1 + a) ^ n = P
      simp only [succ_nsmul, nsmul_eq_mul]
      noncomm_ring
    rw [key]
    have h1 : ‖((1 + a) ^ n - 1 - n • a) * a‖ ≤ ‖a‖ ^ 2 :=
      (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ha).trans ih)
    have h2 : ‖n • (a * a)‖ ≤ ‖a‖ ^ 2 :=
      (norm_nsmul_le_of_ultrametric n _).trans ((norm_mul_le _ _).trans (by rw [sq]))
    exact norm_add_le_of_le_of_le (norm_add_le_of_le_of_le ih h1) h2

variable (ℓ) in
/-- The approximations `ℓ^{-m} (u^{ℓ^m} - 1)` of the `ℓ`-adic logarithm. -/
def logSeq (u : 𝔸) (m : ℕ) : 𝔸 := ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ • (u ^ (ℓ ^ m) - 1)

omit [IsUltrametricDist 𝔸] in
/-- The zeroth approximation of the logarithm is `u - 1`. -/
theorem logSeq_zero (u : 𝔸) : logSeq ℓ u 0 = u - 1 := by
  simp [logSeq]

/-- The prime `ℓ` is nonzero in `ℚ_ℓ`. -/
theorem ell_ne_zero : (ℓ : ℚ_[ℓ]) ≠ 0 := by
  exact_mod_cast (Fact.out : ℓ.Prime).ne_zero

/-- `‖ℓ^{-m}‖ = ℓ ^ m` in `ℚ_ℓ`. -/
theorem norm_ell_pow_inv (m : ℕ) : ‖((ℓ : ℚ_[ℓ]) ^ m)⁻¹‖ = (ℓ : ℝ) ^ m := by
  rw [norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]

/-- `‖ℓ ^ m‖ = ℓ^{-m}` in `ℚ_ℓ`. -/
theorem norm_ell_pow (m : ℕ) : ‖(ℓ : ℚ_[ℓ]) ^ m‖ = ((ℓ : ℝ)⁻¹) ^ m := by
  rw [norm_pow, Padic.norm_p]

omit [IsUltrametricDist 𝔸] in
/-- `u ^ (ℓ ^ m) - 1 = ℓ ^ m • logSeq u m`. -/
theorem pow_sub_one_eq_smul_logSeq (u : 𝔸) (m : ℕ) :
    u ^ (ℓ ^ m) - 1 = ((ℓ : ℚ_[ℓ]) ^ m) • logSeq ℓ u m := by
  rw [logSeq, smul_inv_smul₀ (pow_ne_zero _ ell_ne_zero)]

omit [IsUltrametricDist 𝔸] in
/-- With `a = u^{ℓ^m} - 1`, consecutive approximations differ by
`ℓ^{-(m+1)} ((1 + a) ^ ℓ - 1 - ℓ a)`. -/
theorem logSeq_succ_sub (u : 𝔸) (m : ℕ) :
    logSeq ℓ u (m + 1) - logSeq ℓ u m = ((ℓ : ℚ_[ℓ]) ^ (m + 1))⁻¹ •
      ((1 + (u ^ (ℓ ^ m) - 1)) ^ ℓ - 1 - ℓ • (u ^ (ℓ ^ m) - 1)) := by
  rw [add_sub_cancel, ← pow_mul, ← pow_succ, smul_sub, ← Nat.cast_smul_eq_nsmul ℚ_[ℓ],
    smul_smul]
  have : ((ℓ : ℚ_[ℓ]) ^ (m + 1))⁻¹ * (ℓ : ℚ_[ℓ]) = ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ ell_ne_zero, mul_one]
  rw [this]
  rfl

/-- `ℓ⁻¹ ^ m ≤ 1` in `ℝ`. -/
private theorem inv_ell_pow_le_one (m : ℕ) : ((ℓ : ℝ)⁻¹) ^ m ≤ 1 :=
  pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le))

/-- `ℓ x ≤ 1` if `x ≤ ℓ⁻¹`. -/
private theorem ell_mul_le_one {x : ℝ} (hx : x ≤ (ℓ : ℝ)⁻¹) : ℓ * x ≤ 1 :=
  (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)).trans_eq
    (mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero))

/-- `ℓ⁻¹ ^ m * c` tends to `0`. -/
private theorem tendsto_inv_ell_pow_mul (c : ℝ) :
    Tendsto (fun m : ℕ => ((ℓ : ℝ)⁻¹) ^ m * c) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt))).mul_const c

/-- `ℓ ^ m * (ℓ⁻¹ ^ m * a) ^ 2 = ℓ⁻¹ ^ m * a ^ 2` in `ℝ`. -/
private theorem ell_pow_mul_sq_inv_pow (m : ℕ) (a : ℝ) :
    (ℓ : ℝ) ^ m * (((ℓ : ℝ)⁻¹) ^ m * a) ^ 2 = ((ℓ : ℝ)⁻¹) ^ m * a ^ 2 := by
  have h : (ℓ : ℝ) ^ m * ((ℓ : ℝ)⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero), one_pow]
  linear_combination (((ℓ : ℝ)⁻¹) ^ m * a ^ 2) * h

/-- The binomial estimate applied to `a = u ^ ℓ ^ m - 1` with `‖logSeq u m‖ ≤ δ ≤ ℓ⁻¹`. -/
private theorem pow_mul_norm_one_add_pow_sub_le {u : 𝔸} {m : ℕ} {δ : ℝ} (n : ℕ)
    (hδ : δ ≤ (ℓ : ℝ)⁻¹) (hm : ‖logSeq ℓ u m‖ ≤ δ) :
    (ℓ : ℝ) ^ m * ‖(1 + (u ^ (ℓ ^ m) - 1)) ^ n - 1 - n • (u ^ (ℓ ^ m) - 1)‖ ≤
      ((ℓ : ℝ)⁻¹) ^ m * δ ^ 2 := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hm
  have ha : ‖u ^ (ℓ ^ m) - 1‖ ≤ ((ℓ : ℝ)⁻¹) ^ m * δ := by
    rw [pow_sub_one_eq_smul_logSeq, norm_smul, norm_ell_pow]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have ha1 : ‖u ^ (ℓ ^ m) - 1‖ ≤ 1 :=
    ha.trans ((mul_le_mul (inv_ell_pow_le_one m) (hδ.trans
      (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le))) hδ0
      zero_le_one).trans_eq (one_mul 1))
  calc (ℓ : ℝ) ^ m * ‖(1 + (u ^ (ℓ ^ m) - 1)) ^ n - 1 - n • (u ^ (ℓ ^ m) - 1)‖
      ≤ (ℓ : ℝ) ^ m * (((ℓ : ℝ)⁻¹) ^ m * δ) ^ 2 := by
        gcongr
        exact (norm_one_add_pow_sub_le ha1 n).trans (pow_le_pow_left₀ (norm_nonneg _) ha 2)
    _ = ((ℓ : ℝ)⁻¹) ^ m * δ ^ 2 := ell_pow_mul_sq_inv_pow m δ

/-- The one-step estimate: if `‖logSeq u m‖ ≤ δ ≤ ℓ⁻¹`, the next approximation differs from it
by at most `ℓ δ² ℓ^{-m}`. -/
theorem norm_logSeq_succ_sub_le {u : 𝔸} {m : ℕ} {δ : ℝ} (hδ : δ ≤ (ℓ : ℝ)⁻¹)
    (hm : ‖logSeq ℓ u m‖ ≤ δ) :
    ‖logSeq ℓ u (m + 1) - logSeq ℓ u m‖ ≤ ℓ * δ ^ 2 * ((ℓ : ℝ)⁻¹) ^ m := by
  rw [logSeq_succ_sub, norm_smul, norm_ell_pow_inv]
  calc (ℓ : ℝ) ^ (m + 1) * ‖(1 + (u ^ (ℓ ^ m) - 1)) ^ ℓ - 1 - ℓ • (u ^ (ℓ ^ m) - 1)‖
      = ℓ * ((ℓ : ℝ) ^ m * ‖(1 + (u ^ (ℓ ^ m) - 1)) ^ ℓ - 1 - ℓ • (u ^ (ℓ ^ m) - 1)‖) := by
        ring
    _ ≤ ℓ * (((ℓ : ℝ)⁻¹) ^ m * δ ^ 2) :=
        mul_le_mul_of_nonneg_left (pow_mul_norm_one_add_pow_sub_le ℓ hδ hm) (Nat.cast_nonneg _)
    _ = ℓ * δ ^ 2 * ((ℓ : ℝ)⁻¹) ^ m := by ring

/-- On the disc `‖u - 1‖ ≤ ℓ⁻¹` the approximations stay in the disc of radius `‖u - 1‖`. -/
theorem norm_logSeq_le {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) (m : ℕ) :
    ‖logSeq ℓ u m‖ ≤ ‖u - 1‖ := by
  induction m with
  | zero => rw [logSeq_zero]
  | succ m ih =>
    have hstep := norm_logSeq_succ_sub_le hu ih
    have : ℓ * ‖u - 1‖ ^ 2 * ((ℓ : ℝ)⁻¹) ^ m ≤ ‖u - 1‖ :=
      calc ℓ * ‖u - 1‖ ^ 2 * ((ℓ : ℝ)⁻¹) ^ m ≤ ℓ * ‖u - 1‖ ^ 2 :=
            mul_le_of_le_one_right (by positivity) (inv_ell_pow_le_one m)
        _ = (ℓ * ‖u - 1‖) * ‖u - 1‖ := by ring
        _ ≤ ‖u - 1‖ := mul_le_of_le_one_left (norm_nonneg _) (ell_mul_le_one hu)
    rw [← sub_add_cancel (logSeq ℓ u (m + 1)) (logSeq ℓ u m)]
    exact norm_add_le_of_le_of_le (hstep.trans this) ih

/-- On the disc `‖u - 1‖ ≤ ℓ⁻¹`, consecutive approximations are at distance at most
`ℓ ‖u - 1‖² ℓ^{-m}`. -/
theorem dist_logSeq_succ_le {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) (m : ℕ) :
    dist (logSeq ℓ u m) (logSeq ℓ u (m + 1)) ≤ ℓ * ‖u - 1‖ ^ 2 * ((ℓ : ℝ)⁻¹) ^ m := by
  rw [dist_comm, dist_eq_norm]
  exact norm_logSeq_succ_sub_le hu (norm_logSeq_le hu m)

/-- On the disc `‖u - 1‖ ≤ ℓ⁻¹` the approximations of the logarithm form a Cauchy sequence. -/
theorem cauchySeq_logSeq {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) : CauchySeq (logSeq ℓ u) := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  exact cauchySeq_of_le_geometric _ _ (inv_lt_one_of_one_lt₀ hℓ) (dist_logSeq_succ_le hu)

variable (ℓ) in
/-- **The `ℓ`-adic logarithm** `log u = lim ℓ^{-m} (u^{ℓ^m} - 1)`, meaningful on the disc
`‖u - 1‖ ≤ ℓ⁻¹` (`Stacks.LAdic.tendsto_logSeq`). -/
def ladicLog (u : 𝔸) : 𝔸 := limUnder atTop (logSeq ℓ u)

variable [CompleteSpace 𝔸]

/-- On the disc `‖u - 1‖ ≤ ℓ⁻¹` the approximations `ℓ^{-m} (u^{ℓ^m} - 1)` converge to
`ladicLog ℓ u`. -/
theorem tendsto_logSeq {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) :
    Tendsto (logSeq ℓ u) atTop (𝓝 (ladicLog ℓ u)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_logSeq hu))

omit [CompleteSpace 𝔸] [IsUltrametricDist 𝔸] in
/-- The logarithm is the limit of any limit of its approximations. -/
theorem ladicLog_eq_of_tendsto {u L : 𝔸} (h : Tendsto (logSeq ℓ u) atTop (𝓝 L)) :
    ladicLog ℓ u = L :=
  h.limUnder_eq

/-- `‖log u‖ ≤ ‖u - 1‖`. -/
theorem norm_ladicLog_le {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) : ‖ladicLog ℓ u‖ ≤ ‖u - 1‖ :=
  le_of_tendsto (tendsto_logSeq hu).norm (Eventually.of_forall (norm_logSeq_le hu))

/-- **The first-order estimate** `‖log u - (u - 1)‖ ≤ ℓ ‖u - 1‖²`. -/
theorem norm_ladicLog_sub_le {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) :
    ‖ladicLog ℓ u - (u - 1)‖ ≤ ℓ * ‖u - 1‖ ^ 2 := by
  have hall : ∀ m, ‖logSeq ℓ u m - (u - 1)‖ ≤ ℓ * ‖u - 1‖ ^ 2 := by
    intro m
    induction m with
    | zero =>
      rw [logSeq_zero, sub_self, norm_zero]
      positivity
    | succ m ih =>
      have hstep : ‖logSeq ℓ u (m + 1) - logSeq ℓ u m‖ ≤ ℓ * ‖u - 1‖ ^ 2 :=
        (norm_logSeq_succ_sub_le hu (norm_logSeq_le hu m)).trans
          (mul_le_of_le_one_right (by positivity) (inv_ell_pow_le_one m))
      calc ‖logSeq ℓ u (m + 1) - (u - 1)‖
          = ‖(logSeq ℓ u (m + 1) - logSeq ℓ u m) + (logSeq ℓ u m - (u - 1))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le_of_le_of_le hstep ih
  exact le_of_tendsto ((tendsto_logSeq hu).sub_const (u - 1)).norm (Eventually.of_forall hall)

/-- **The logarithm has no kernel** on the open disc `‖u - 1‖ < ℓ⁻¹`. -/
theorem eq_one_of_ladicLog_eq_zero {u : 𝔸} (hu : ‖u - 1‖ < (ℓ : ℝ)⁻¹)
    (h : ladicLog ℓ u = 0) : u = 1 := by
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
  have hb := norm_ladicLog_sub_le hu.le
  rw [h, zero_sub, norm_neg] at hb
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have : 1 ≤ ℓ * ‖u - 1‖ := by
    rw [sq, ← mul_assoc] at hb
    exact (le_mul_iff_one_le_left hpos).mp hb
  have : (ℓ : ℝ) * ‖u - 1‖ < 1 :=
    (mul_lt_mul_of_pos_left hu hℓ).trans_eq (mul_inv_cancel₀ hℓ.ne')
  linarith

/-- **The logarithm of a product of commuting elements** is the sum of the logarithms. -/
theorem ladicLog_mul_of_commute {u v : 𝔸} (huv : Commute u v) (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹)
    (hv : ‖v - 1‖ ≤ (ℓ : ℝ)⁻¹) : ladicLog ℓ (u * v) = ladicLog ℓ u + ladicLog ℓ v := by
  refine ladicLog_eq_of_tendsto ?_
  have hc : (ℓ : ℚ_[ℓ]) ≠ 0 := ell_ne_zero
  have key : ∀ m, logSeq ℓ (u * v) m = logSeq ℓ u m + logSeq ℓ v m +
      ((ℓ : ℚ_[ℓ]) ^ m) • (logSeq ℓ u m * logSeq ℓ v m) := by
    intro m
    have hpow : (u * v) ^ (ℓ ^ m) - 1 = (u ^ (ℓ ^ m) - 1) + (v ^ (ℓ ^ m) - 1) +
        (u ^ (ℓ ^ m) - 1) * (v ^ (ℓ ^ m) - 1) := by
      rw [huv.mul_pow]
      noncomm_ring
    rw [logSeq, hpow, pow_sub_one_eq_smul_logSeq u m, pow_sub_one_eq_smul_logSeq v m,
      smul_mul_smul_comm, smul_add, smul_add, inv_smul_smul₀ (pow_ne_zero _ hc),
      inv_smul_smul₀ (pow_ne_zero _ hc), smul_smul, inv_mul_cancel_left₀ (pow_ne_zero _ hc)]
  rw [show logSeq ℓ (u * v) = _ from funext key]
  have hzero : Tendsto (fun m => ((ℓ : ℚ_[ℓ]) ^ m) • (logSeq ℓ u m * logSeq ℓ v m)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (a := fun m => ((ℓ : ℝ)⁻¹) ^ m * (‖u - 1‖ * ‖v - 1‖)) ?_ ?_
    · intro m
      rw [norm_smul, norm_ell_pow]
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul (norm_logSeq_le hu m) (norm_logSeq_le hv m)
        (norm_nonneg _) (norm_nonneg _))
    · exact tendsto_inv_ell_pow_mul _
  simpa using ((tendsto_logSeq hu).add (tendsto_logSeq hv)).add hzero

/-- `log (u ^ n) = n • log u`. -/
theorem ladicLog_pow {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) (n : ℕ) :
    ladicLog ℓ (u ^ n) = n • ladicLog ℓ u := by
  refine ladicLog_eq_of_tendsto ?_
  have key : ∀ m, logSeq ℓ (u ^ n) m - n • logSeq ℓ u m = ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ •
      ((1 + (u ^ (ℓ ^ m) - 1)) ^ n - 1 - n • (u ^ (ℓ ^ m) - 1)) := by
    intro m
    rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, smul_sub, smul_sub, logSeq, logSeq,
      smul_comm _ n]
    simp only [smul_sub]
  have hzero : Tendsto (fun m => logSeq ℓ (u ^ n) m - n • logSeq ℓ u m) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun m => ((ℓ : ℝ)⁻¹) ^ m * ‖u - 1‖ ^ 2) ?_ ?_
    · intro m
      rw [key, norm_smul, norm_ell_pow_inv]
      exact pow_mul_norm_one_add_pow_sub_le n hu (norm_logSeq_le hu m)
    · exact tendsto_inv_ell_pow_mul _
  simpa using hzero.add ((tendsto_logSeq hu).const_smul n)

/-- **Continuous algebra maps commute with the logarithm.** -/
theorem map_ladicLog {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℚ_[ℓ] 𝔹] {F : Type*}
    [FunLike F 𝔸 𝔹] [AlgHomClass F ℚ_[ℓ] 𝔸 𝔹] (f : F) (hf : Continuous f) {u : 𝔸}
    (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) : f (ladicLog ℓ u) = ladicLog ℓ (f u) := by
  refine (ladicLog_eq_of_tendsto ?_).symm
  have : logSeq ℓ (f u) = fun m => f (logSeq ℓ u m) := by
    funext m
    simp [logSeq, map_smul, map_sub, map_pow, map_one]
  rw [this]
  exact (hf.tendsto _).comp (tendsto_logSeq hu)

/-- **The logarithm stays in closed subalgebras.** -/
theorem ladicLog_mem {S : Subalgebra ℚ_[ℓ] 𝔸} (hS : IsClosed (S : Set 𝔸)) {u : 𝔸} (huS : u ∈ S)
    (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) : ladicLog ℓ u ∈ S :=
  hS.mem_of_tendsto (tendsto_logSeq hu) (Eventually.of_forall fun _ =>
    S.smul_mem (S.sub_mem (S.pow_mem huS _) S.one_mem) _)

/-- The logarithm of `u` commutes with everything that commutes with `u`. -/
theorem Commute.ladicLog_left {u w : 𝔸} (h : Commute u w) (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) :
    Commute (ladicLog ℓ u) w := by
  have hcl : IsClosed {x : 𝔸 | x * w = w * x} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  refine hcl.mem_of_tendsto (tendsto_logSeq hu) (Eventually.of_forall fun m => ?_)
  exact (((h.pow_left _).sub_left (Commute.one_left w)).smul_left _).eq

/-! ### The exponential -/

open NormedSpace

/-- `n!` is nonzero in `ℚ_ℓ`. -/
theorem factorial_cast_ne_zero (n : ℕ) : ((n.factorial : ℕ) : ℚ_[ℓ]) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

/-- `‖1 / n!‖ = ℓ ^ v_ℓ(n!)` in `ℚ_ℓ`. -/
theorem norm_inv_factorial (n : ℕ) :
    ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ = (ℓ : ℝ) ^ padicValNat ℓ n.factorial := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (factorial_cast_ne_zero n),
    Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]

/-- Legendre: `‖1 / n!‖ ≤ ℓ ^ (n - 1)` for `n ≥ 1`. -/
theorem norm_inv_factorial_le_pow_pred {n : ℕ} (hn : n ≠ 0) :
    ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ ≤ (ℓ : ℝ) ^ (n - 1) := by
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le
  rw [norm_inv_factorial]
  exact pow_le_pow_right₀ hℓ (Nat.le_sub_one_of_lt (padicValNat_factorial_lt_of_ne_zero ℓ hn))

/-- `‖1 / n!‖ ≤ ℓ ^ n` in `ℚ_ℓ`. -/
theorem norm_inv_factorial_le (n : ℕ) :
    ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ ≤ (ℓ : ℝ) ^ n := by
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le
  rw [norm_inv_factorial]
  exact pow_le_pow_right₀ hℓ (padicValNat_factorial_le ℓ n)

omit [IsUltrametricDist 𝔸] [CompleteSpace 𝔸] in
/-- The exponential series of a normed `ℚ_ℓ`-algebra has radius of convergence at least
`ℓ⁻¹`. -/
theorem le_radius_expSeries :
    (((ℓ : NNReal)⁻¹ : NNReal) : ENNReal) ≤ (expSeries ℚ_[ℓ] 𝔸).radius := by
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
  refine FormalMultilinearSeries.le_radius_of_bound _ (max 1 ‖(1 : 𝔸)‖) fun n => ?_
  rw [expSeries, norm_smul]
  have h1 := ContinuousMultilinearMap.norm_mkPiAlgebraFin_le (𝕜 := ℚ_[ℓ]) (n := n) (A := 𝔸)
  have h2 : ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ * (((ℓ : NNReal)⁻¹ : NNReal) : ℝ) ^ n ≤ 1 := by
    rw [NNReal.coe_inv, NNReal.coe_natCast]
    calc ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ * ((ℓ : ℝ)⁻¹) ^ n ≤ (ℓ : ℝ) ^ n * ((ℓ : ℝ)⁻¹) ^ n := by
          gcongr
          exact norm_inv_factorial_le n
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hℓ.ne', one_pow]
  calc ‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[ℓ] n 𝔸‖ *
        (((ℓ : NNReal)⁻¹ : NNReal) : ℝ) ^ n
      = (‖((n.factorial : ℕ) : ℚ_[ℓ])⁻¹‖ * (((ℓ : NNReal)⁻¹ : NNReal) : ℝ) ^ n) *
          ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[ℓ] n 𝔸‖ := by ring
    _ ≤ 1 * max 1 ‖(1 : 𝔸)‖ := by gcongr
    _ = max 1 ‖(1 : 𝔸)‖ := one_mul _

omit [IsUltrametricDist 𝔸] [CompleteSpace 𝔸] in
/-- The open disc `‖x‖ < ℓ⁻¹` lies in the disc of convergence of the exponential. -/
theorem mem_eball_expSeries {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) :
    x ∈ Metric.eball (0 : 𝔸) (expSeries ℚ_[ℓ] 𝔸).radius := by
  refine lt_of_lt_of_le ?_ le_radius_expSeries
  have h : ‖x‖₊ < (ℓ : NNReal)⁻¹ := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_inv, NNReal.coe_natCast]
    exact hx
  rw [edist_zero_right, enorm_eq_nnnorm]
  exact ENNReal.coe_lt_coe.mpr h

omit [IsUltrametricDist 𝔸] [CompleteSpace 𝔸] in
/-- On the disc `‖x‖ < ℓ⁻¹` the series `∑ xⁿ / n!` sums to `exp x`. -/
theorem hasSum_exp {x : 𝔸} [CompleteSpace 𝔸] (hx : ‖x‖ < (ℓ : ℝ)⁻¹) :
    HasSum (fun n => (((n.factorial : ℕ) : ℚ_[ℓ])⁻¹) • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' (𝕂 := ℚ_[ℓ]) x (mem_eball_expSeries hx)

omit [IsUltrametricDist 𝔸] [CompleteSpace 𝔸] in
/-- For `‖x‖ < ℓ⁻¹` and `k ≥ 2`, the term `xᵏ / k!` of the exponential series has norm at most
`ℓ ‖x‖²`. -/
theorem norm_inv_factorial_smul_pow_le {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) (n : ℕ) :
    ‖(((n + 2).factorial : ℕ) : ℚ_[ℓ])⁻¹ • x ^ (n + 2)‖ ≤ ℓ * ‖x‖ ^ 2 := by
  have hlx : ℓ * ‖x‖ ≤ 1 := ell_mul_le_one hx.le
  have h1 : ‖(((n + 2).factorial : ℕ) : ℚ_[ℓ])⁻¹‖ ≤ (ℓ : ℝ) ^ (n + 1) :=
    norm_inv_factorial_le_pow_pred (n := n + 2) (by omega)
  have h2 : ‖x ^ (n + 2)‖ ≤ ‖x‖ ^ (n + 2) := norm_pow_le' _ (by omega)
  rw [norm_smul]
  calc ‖(((n + 2).factorial : ℕ) : ℚ_[ℓ])⁻¹‖ * ‖x ^ (n + 2)‖
      ≤ (ℓ : ℝ) ^ (n + 1) * ‖x‖ ^ (n + 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ℓ * ‖x‖ ^ 2 * (ℓ * ‖x‖) ^ n := by ring
    _ ≤ ℓ * ‖x‖ ^ 2 := mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hlx)

/-- **The second-order estimate** `‖exp x - 1 - x‖ ≤ ℓ ‖x‖²` on `‖x‖ < ℓ⁻¹`. -/
theorem norm_exp_sub_one_sub_le {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) :
    ‖exp x - 1 - x‖ ≤ ℓ * ‖x‖ ^ 2 := by
  have hs : HasSum (fun n => (((n + 2).factorial : ℕ) : ℚ_[ℓ])⁻¹ • x ^ (n + 2))
      (exp x - ∑ i ∈ Finset.range 2, (((i.factorial : ℕ) : ℚ_[ℓ])⁻¹) • x ^ i) :=
    (hasSum_nat_add_iff' 2).mpr (hasSum_exp hx)
  have h01 : ∑ i ∈ Finset.range 2, (((i.factorial : ℕ) : ℚ_[ℓ])⁻¹) • x ^ i = 1 + x := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero, pow_one, zero_add]
  rw [h01, sub_add_eq_sub_sub] at hs
  rw [← hs.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (norm_inv_factorial_smul_pow_le hx)

/-- `‖exp x - 1‖ ≤ ‖x‖` on the disc `‖x‖ < ℓ⁻¹`. -/
theorem norm_exp_sub_one_le {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) : ‖exp x - 1‖ ≤ ‖x‖ := by
  have h2 : ℓ * ‖x‖ ^ 2 ≤ ‖x‖ := by
    have := ell_mul_le_one hx.le
    nlinarith [norm_nonneg x]
  calc ‖exp x - 1‖ = ‖(exp x - 1 - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖x‖ := norm_add_le_of_le_of_le ((norm_exp_sub_one_sub_le hx).trans h2) le_rfl

/-- `exp (n • x) = exp x ^ n` on the disc `‖x‖ < ℓ⁻¹`. -/
theorem exp_nsmul_of_norm_lt {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) (n : ℕ) :
    exp (n • x) = exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, pow_succ, exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ])
      ((Commute.refl x).smul_left n)
      (mem_eball_expSeries ((norm_nsmul_le_of_ultrametric n x).trans_lt hx))
      (mem_eball_expSeries hx), ih]

/-- **`log (exp x) = x`** on the disc `‖x‖ < ℓ⁻¹`. -/
theorem ladicLog_exp {x : 𝔸} (hx : ‖x‖ < (ℓ : ℝ)⁻¹) : ladicLog ℓ (exp x) = x := by
  refine ladicLog_eq_of_tendsto ?_
  have hc : (ℓ : ℚ_[ℓ]) ≠ 0 := ell_ne_zero
  have key : ∀ m, logSeq ℓ (exp x) m - x = ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ •
      (exp (((ℓ : ℚ_[ℓ]) ^ m) • x) - 1 - ((ℓ : ℚ_[ℓ]) ^ m) • x) := by
    intro m
    have hn : ((ℓ : ℚ_[ℓ]) ^ m) • x = (ℓ ^ m : ℕ) • x := by
      rw [← Nat.cast_smul_eq_nsmul ℚ_[ℓ], Nat.cast_pow]
    rw [logSeq, ← exp_nsmul_of_norm_lt hx, ← hn, smul_sub, smul_sub,
      inv_smul_smul₀ (pow_ne_zero _ hc)]
    simp only [smul_sub]
  have hy : ∀ m, ‖((ℓ : ℚ_[ℓ]) ^ m) • x‖ = ((ℓ : ℝ)⁻¹) ^ m * ‖x‖ := fun m => by
    rw [norm_smul, norm_ell_pow]
  have hyl : ∀ m, ‖((ℓ : ℚ_[ℓ]) ^ m) • x‖ < (ℓ : ℝ)⁻¹ := fun m => by
    rw [hy]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (inv_ell_pow_le_one m)) hx
  have hzero : Tendsto (fun m => logSeq ℓ (exp x) m - x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun m => ((ℓ : ℝ)⁻¹) ^ m * (ℓ * ‖x‖ ^ 2)) ?_ ?_
    · intro m
      rw [key, norm_smul, norm_ell_pow_inv]
      calc (ℓ : ℝ) ^ m * ‖exp (((ℓ : ℚ_[ℓ]) ^ m) • x) - 1 - ((ℓ : ℚ_[ℓ]) ^ m) • x‖
          ≤ (ℓ : ℝ) ^ m * (ℓ * (((ℓ : ℝ)⁻¹) ^ m * ‖x‖) ^ 2) := by
            gcongr
            rw [← hy]
            exact norm_exp_sub_one_sub_le (hyl m)
        _ = ((ℓ : ℝ)⁻¹) ^ m * (ℓ * ‖x‖ ^ 2) := by
            rw [mul_left_comm, ell_pow_mul_sq_inv_pow]; ring
    · exact tendsto_inv_ell_pow_mul _
  simpa using hzero.add_const x

/-- **`exp (log u) = u`** on the disc `‖u - 1‖ < ℓ⁻¹`. -/
theorem exp_ladicLog {u : 𝔸} (hu : ‖u - 1‖ < (ℓ : ℝ)⁻¹) : exp (ladicLog ℓ u) = u := by
  set L := ladicLog ℓ u with hL
  have hLn : ‖L‖ < (ℓ : ℝ)⁻¹ := (norm_ladicLog_le hu.le).trans_lt hu
  have hLn' : ‖-L‖ < (ℓ : ℝ)⁻¹ := by rwa [norm_neg]
  have hcomm : Commute (exp (-L)) u :=
    ((Commute.ladicLog_left (ℓ := ℓ) (Commute.refl u) hu.le).neg_left).exp_left
  have he : ‖exp (-L) - 1‖ < (ℓ : ℝ)⁻¹ := (norm_exp_sub_one_le hLn').trans_lt hLn'
  have hu1 : ‖u - 1‖ ≤ 1 := hu.le.trans (inv_le_one_of_one_le₀
    (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le))
  have hw : exp (-L) * u = 1 := by
    refine eq_one_of_ladicLog_eq_zero (ℓ := ℓ) ?_ ?_
    · have : exp (-L) * u - 1 = (exp (-L) - 1) * (u - 1) + (exp (-L) - 1) + (u - 1) := by
        noncomm_ring
      rw [this]
      refine lt_of_le_of_lt (norm_add_le_of_le_of_le (r := max ‖exp (-L) - 1‖ ‖u - 1‖)
        (norm_add_le_of_le_of_le ?_ (le_max_left _ _)) (le_max_right _ _)) (max_lt he hu)
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hu1).trans
        (le_max_left _ _))
    · rw [ladicLog_mul_of_commute hcomm he.le hu.le, ladicLog_exp hLn', ← hL, neg_add_cancel]
  calc exp L = exp L * (exp (-L) * u) := by rw [hw, mul_one]
    _ = exp (L + -L) * u := by
        rw [← mul_assoc, exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) (Commute.neg_right
          (Commute.refl L)) (mem_eball_expSeries hLn) (mem_eball_expSeries hLn')]
    _ = u := by rw [add_neg_cancel, exp_zero, one_mul]

end Stacks.LAdic
