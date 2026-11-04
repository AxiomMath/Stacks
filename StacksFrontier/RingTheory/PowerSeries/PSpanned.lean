module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.PowerSeries.Expand
public import StacksFrontier.FieldTheory.PSpanningRoot

/-!
# Power series over a perfect field are `p`-spanned by the variable

For a perfect field `κ` of characteristic `p`,

$$ \kappa[[X]] = \kappa[[X]]^p \oplus \kappa[[X]]^p X \oplus \dots
  \oplus \kappa[[X]]^p X^{p-1}, $$

that is, `IsPSpannedBy p (X : PowerSeries κ)`. Explicitly: the `p`-th powers in `κ[[X]]` are the
series supported in exponents divisible by `p`, with `p`-th-power coefficients — and over a
perfect field the coefficient condition is vacuous, so splitting a series by the residue of its
exponent modulo `p` writes it in the required form.

This is the single place where perfectness of the residue field is spent in the proof of
condition (b) of [Stacks: Tag 09F9](https://stacks.math.columbia.edu/tag/09F9): composed with the
equal-characteristic structure theorem `κ_A⟦X⟧ ≃+* A` sending `X` to a chosen uniformizer, it
gives `IsPSpannedBy p π` for a complete discrete valuation ring of equal characteristic with
perfect residue field, and hence for its fraction field.

## Main results

* `PowerSeries.isPSpannedBy_X`.
-/

@[expose] public section

open PowerSeries

/-- **`κ⟦X⟧` is `p`-spanned by `X` when `κ` is perfect of characteristic `p`.**

The `i`-th component of `f` is the series `∑_m (coeff (m * p + i) f) X ^ m` with each coefficient
replaced by its (unique) `p`-th root; `PowerSeries.map_frobenius_expand` identifies the `p`-th
power of that with the `X ↦ X ^ p` expansion, and the claim becomes the observation that for each
`n` exactly one `i < p` satisfies `i ≤ n` and `p ∣ n - i`. -/
theorem PowerSeries.isPSpannedBy_X {κ : Type*} [Field κ] (p : ℕ) [hp : Fact p.Prime] [CharP κ p]
    [PerfectField κ] : IsPSpannedBy p (X : PowerSeries κ) := by
  intro f
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hppos : 0 < p := hp.out.pos
  have : ExpChar κ p := .prime hp.out
  have : PerfectRing κ p := PerfectField.toPerfectRing p
  set σ : κ →+* κ := (frobeniusEquiv κ p).symm.toRingHom with hσ
  have hσfrob : ∀ x : κ, frobenius κ p (σ x) = x := by
    intro x; simp [hσ, ← frobeniusEquiv_apply]
  refine ⟨fun i => PowerSeries.map σ (PowerSeries.mk fun m => PowerSeries.coeff (m * p + i) f), ?_⟩
  have key : ∀ i : Fin p,
      (PowerSeries.map σ (PowerSeries.mk fun m => PowerSeries.coeff (m * p + i) f)) ^ p
        = PowerSeries.expand p hp0 (PowerSeries.mk fun m => PowerSeries.coeff (m * p + i) f) := by
    intro i
    rw [← PowerSeries.map_frobenius_expand p hp0, ← PowerSeries.map_expand]
    refine PowerSeries.ext fun n => ?_
    simp only [PowerSeries.coeff_map]
    exact hσfrob _
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
  refine (PowerSeries.ext fun n => ?_).symm
  simp only [map_sum, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_expand,
    PowerSeries.coeff_mk]
  obtain ⟨q, r, hr, hn⟩ : ∃ q r, r < p ∧ n = q * p + r :=
    ⟨n / p, n % p, Nat.mod_lt _ hppos, (Nat.div_add_mod' n p).symm⟩
  have hsub : n - r = p * q := by subst hn; simp [mul_comm]
  have hdiv : (n - r) / p = q := by rw [hsub]; exact Nat.mul_div_cancel_left q hppos
  rw [Finset.sum_eq_single_of_mem (⟨r, hr⟩ : Fin p) (Finset.mem_univ _) ?_]
  · split_ifs with h1 h2
    · rw [hdiv, hn]
    · exact absurd ⟨q, hsub⟩ h2
    · exact absurd (show r ≤ n by omega) h1
  · intro b _ hb
    split_ifs with h1 h2
    · refine absurd (Fin.ext (show (b : ℕ) = r from ?_)) hb
      have hmod : (b : ℕ) % p = n % p := (Nat.modEq_iff_dvd' h1).mpr h2
      rw [Nat.mod_eq_of_lt b.2] at hmod
      have hnr : n % p = r := by
        rw [hn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      omega
    · rfl
    · rfl
