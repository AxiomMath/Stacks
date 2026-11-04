module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Ring

/-!
# Shrinking a finite-index subgroup by a cyclic quotient of large order

Let `H` be a subgroup of index `e` of a group `G` and `χ : G → ℤ/n^(e+1)` a surjective
homomorphism. Then `n` divides the index of `H ∩ ker χ` in `H`: that index is `#χ(H)`, and
`χ(H)` has index `c` dividing both `e` and `n^(e+1)`. Every prime `ℓ` occurs in `c` with
exponent at most its exponent in `e`, which is less than `e`, so `c ∣ n^e` and
`#χ(H) = n^(e+1)/c` is divisible by `n`. Only powers of `n` occur, so `ℤ/n^(e+1)` is a quotient
of the prime-to-`p` part of a fundamental group whenever `n` is prime to `p`.

In the proof of Tag 03VM, `G = π₁(X_{k̄})`, `H` is the fundamental group of a connected finite
étale cover `A` of `X_{k̄}` and `χ` comes from a cyclic cover of `X_{k̄}`; the subgroup
`H ∩ ker χ` gives a connected cover of `A` of degree divisible by `n`, on which the trace kills
`H²` with coefficients killed by `n`.

## Main results

* `Nat.dvd_pow_of_dvd_of_dvd_pow_succ` — `c ∣ e` and `c ∣ n^(e+1)` give `c ∣ n^e`.
* `Subgroup.dvd_relIndex_inf_ker_of_surjective` — the divisibility.
-/

@[expose] public section

namespace Nat

/-- **`c ∣ e` and `c ∣ n^(e+1)` give `c ∣ n^e`**, for `e ≠ 0` and `n ≠ 0`: the exponent of a
prime in `c` is at most its exponent in `e`, which is less than `e`. -/
theorem dvd_pow_of_dvd_of_dvd_pow_succ {c e n : ℕ} (he : e ≠ 0) (hn : n ≠ 0) (hce : c ∣ e)
    (hcn : c ∣ n ^ (e + 1)) : c ∣ n ^ e := by
  have hc : c ≠ 0 := fun h => he (Nat.eq_zero_of_zero_dvd (h ▸ hce))
  rw [← Nat.factorization_le_iff_dvd hc (pow_ne_zero _ hn)]
  intro ℓ
  have h1 := (Nat.factorization_le_iff_dvd hc (pow_ne_zero _ hn)).2 hcn ℓ
  have h2 := (Nat.factorization_le_iff_dvd hc he).2 hce ℓ
  have h3 : e.factorization ℓ < e := Nat.factorization_lt ℓ he
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1 ⊢
  rcases Nat.eq_zero_or_pos (n.factorization ℓ) with h0 | h0
  · rw [h0, mul_zero] at h1 ⊢
    exact h1
  · exact (h2.trans_lt h3).le.trans (Nat.le_mul_of_pos_right e h0)

end Nat

namespace Subgroup

/-- **`n` divides `[H : H ∩ ker χ]`** for `χ : G → ℤ/n^([G : H] + 1)` surjective. -/
theorem dvd_relIndex_inf_ker_of_surjective {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) [NeZero n] (χ : G →* Multiplicative (ZMod (n ^ (H.index + 1))))
    (hχ : Function.Surjective χ) : n ∣ (H ⊓ χ.ker).relIndex H := by
  rw [inf_relIndex_left, relIndex_ker]
  have hN : NeZero (n ^ (H.index + 1)) := ⟨pow_ne_zero _ (NeZero.ne n)⟩
  have : Finite (Multiplicative (ZMod (n ^ (H.index + 1)))) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have hcard : Nat.card (Multiplicative (ZMod (n ^ (H.index + 1)))) = n ^ (H.index + 1) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h2 := (H.map χ).card_mul_index
  rw [hcard] at h2
  have hi : (H.map χ).index ≠ 0 := (H.map χ).index_ne_zero_of_finite
  have hce : (H.map χ).index ∣ H.index := H.index_map_dvd hχ
  have hcn : (H.map χ).index ∣ n ^ (H.index + 1) := Dvd.intro_left _ h2
  obtain ⟨j, hj⟩ := Nat.dvd_pow_of_dvd_of_dvd_pow_succ FiniteIndex.index_ne_zero (NeZero.ne n)
    hce hcn
  have hN' : n ^ (H.index + 1) = n * j * (H.map χ).index := by
    generalize (H.map χ).index = c at hj ⊢
    rw [pow_succ, hj]
    ring
  exact ⟨j, Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) (h2.trans hN')⟩

end Subgroup
