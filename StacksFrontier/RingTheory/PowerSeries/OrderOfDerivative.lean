module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Vanishing order from iterated derivatives

Let `K` be a field and `u ∈ K⟦X⟧` a power series with nonzero constant term. Write
`D F = u · F'` for the twisted derivative. If `k` is such that `1, …, k - 1` are nonzero in `K`
(for instance `k ≤ p` in characteristic `p`), and the constant terms of `F, D F, …, D^{k-1} F` all
vanish, then `F` has order at least `k`. This is the form in which Stepanov's method uses
derivatives along a plane curve: at a smooth point the derivation `Ψ_Y ∂_X - Ψ_X ∂_Y` becomes
`u · d/ds` on the branch, with `u` the value of `Ψ_Y` there.

## Main results

* `PowerSeries.order_mul_derivative_eq`: `D` lowers an order `t + 1` to `t` when `t + 1 ≠ 0`.
* `PowerSeries.nat_le_order_of_constantCoeff_iterate_eq_zero`: the vanishing criterion.
-/

@[expose] public section

namespace PowerSeries

variable {K : Type*} [Field K]

/-- If `F` has order `t + 1` and `t + 1 ≠ 0` in `K`, then `u * F'` has order `t` for any `u`
with nonzero constant term. -/
theorem order_mul_derivative_eq {u F : K⟦X⟧} (hu : constantCoeff u ≠ 0) {t : ℕ}
    (hF : F.order = (t + 1 : ℕ)) (ht : ((t + 1 : ℕ) : K) ≠ 0) :
    (u * d⁄dX F).order = t := by
  have hu0 : u.order = 0 := by
    by_contra h
    exact hu (order_ne_zero_iff_constCoeff_eq_zero.mp h)
  rw [order_mul, hu0, zero_add, order_eq_nat]
  obtain ⟨h1, h2⟩ := order_eq_nat.mp hF
  refine ⟨?_, fun i hi => ?_⟩
  · rw [coeff_derivative]
    exact mul_ne_zero h1 (by exact_mod_cast ht)
  · rw [coeff_derivative, h2 (i + 1) (by omega), zero_mul]

/-- **Vanishing order from iterated twisted derivatives.** Let `u` have nonzero constant term and
let `D F = u * F'`. If `1, …, k - 1` are nonzero in `K` and the constant terms of
`F, D F, …, D^{k-1} F` vanish, then `F` has order at least `k`. -/
theorem nat_le_order_of_constantCoeff_iterate_eq_zero {u : K⟦X⟧} (hu : constantCoeff u ≠ 0)
    (F : K⟦X⟧) {k : ℕ} (hk : ∀ t : ℕ, 0 < t → t < k → (t : K) ≠ 0)
    (h : ∀ j < k, constantCoeff ((fun G => u * d⁄dX G)^[j] F) = 0) :
    (k : ℕ∞) ≤ F.order := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, F.order = r := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt) |>.imp
    fun _ h => h.symm
  have hrk : r < k := by exact_mod_cast hr ▸ hlt
  have key : ∀ i ≤ r, ((fun G => u * d⁄dX G)^[i] F).order = (r - i : ℕ) := by
    intro i hi
    induction i with
    | zero => simpa using hr
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have h' := ih (by omega)
      rw [show r - i = (r - (i + 1)) + 1 by omega] at h'
      exact order_mul_derivative_eq hu h' (hk _ (by omega) (by omega))
  have h0 := key r le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at h0
  exact (order_ne_zero_iff_constCoeff_eq_zero.mpr (h r hrk)) h0

end PowerSeries
