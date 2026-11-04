module

public import StacksFrontier.RingTheory.Rig.PrincipalLiftUniform

/-!
# Moving an approximate vector into the kernel of a quasi-idempotent

Let `R` be a Noetherian ring, `α ∈ R`, and `P` a square matrix over `R` with `P² = αᶜ P`, so that
off `V(α)` the matrix `α⁻ᶜ P` is an idempotent. If a vector `t̃` satisfies `P t̃ ≡ 0` modulo a high
power `αⁿ`, then a small correction of `t̃` lies exactly in the kernel of `P`.

Write `P t̃ = αⁿ w`. Then `t := t̃ − αⁿ⁻ᶜ w` works: `P² t̃ = αᶜ P t̃` gives `αⁿ (P w − αᶜ w) = 0`,
so `P t = −αⁿ⁻ᶜ (P w − αᶜ w)` is `α`-power torsion. It also lies in `(α)ⁿ⁻ᶜ`, so it vanishes once
`n − c` exceeds an Artin–Rees constant for the `α`-power torsion of `R`.

## Main results

* `Rig.exists_mulVec_eq_zero_of_mulVec_mem`: the correction, with a threshold depending only on
  `R`, `α` and `c`.
-/

@[expose] public section

namespace Rig

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- **Correcting into the kernel of a quasi-idempotent.** For `α ∈ R` and `c` there is `n₀` such
that for every `n ≥ n₀`, every matrix `P` with `P * P = αᶜ • P` and every vector `t̃` with
`P t̃ ∈ (α)ⁿ` there is `t ≡ t̃ mod (α)ⁿ⁻ᶜ` with `P t = 0`. -/
theorem exists_mulVec_eq_zero_of_mulVec_mem (α : R) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ {N : ℕ} (P : Matrix (Fin N) (Fin N) R), P * P = α ^ c • P →
      ∀ t' : Fin N → R, (∀ i, P.mulVec t' i ∈ Ideal.span {α} ^ n) →
        ∃ t : Fin N → R, P.mulVec t = 0 ∧ ∀ i, t i - t' i ∈ Ideal.span {α} ^ (n - c) := by
  obtain ⟨k₀, hk₀⟩ := exists_disjoint_torsionIdeal_pow_span_singleton α
  refine ⟨c + k₀, fun n hn N P hP t' ht' ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + c := ⟨n - c, by omega⟩
  rw [Nat.add_sub_cancel]
  have hw : ∀ i, ∃ w : R, P.mulVec t' i = α ^ (m + c) * w := fun i ↦ by
    have := ht' i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, by rw [← hw, mul_comm]⟩
  choose w hw using hw
  have hPw : ∀ i, α ^ (m + c) * ((P.mulVec w) i - α ^ c * w i) = 0 := by
    intro i
    have h1 : P.mulVec (P.mulVec t') = α ^ c • P.mulVec t' := by
      rw [Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]
    have h2 : P.mulVec t' = α ^ (m + c) • w :=
      funext fun j ↦ by rw [hw j, Pi.smul_apply, smul_eq_mul]
    rw [h2, Matrix.mulVec_smul] at h1
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [mul_sub, this]
    ring
  have hmem : ∀ a b : ℕ, ∀ x : R, b ≤ a → α ^ a * x ∈ Ideal.span {α} ^ b := fun a b x h ↦
    Ideal.mul_mem_right _ _
      (Ideal.pow_le_pow_right h (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self α) a))
  refine ⟨t' - α ^ m • w, ?_, fun i ↦ ?_⟩
  · funext i
    have htor : α ^ m * ((P.mulVec w) i - α ^ c * w i) ∈ torsionIdeal R α :=
      (mem_torsionIdeal_iff R α _).mpr ⟨m + c, by rw [← mul_assoc, ← pow_add,
        add_comm, pow_add, mul_assoc, hPw i, mul_zero]⟩
    have h0 := hk₀.le_bot ⟨htor, hmem _ _ _ (by omega)⟩
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hw i,
      Pi.zero_apply, pow_add, show α ^ m * α ^ c * w i - α ^ m * (P.mulVec w) i =
        -(α ^ m * ((P.mulVec w) i - α ^ c * w i)) by ring, Ideal.mem_bot.mp h0, neg_zero]
  · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, neg_mem_iff]
    exact hmem _ _ _ le_rfl

end Rig
