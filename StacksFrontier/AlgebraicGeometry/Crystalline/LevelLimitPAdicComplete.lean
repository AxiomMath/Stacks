module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# Completeness of a limit of levels cut out at a shifted exponent

Let `I` be a finitely generated ideal of `A` and `(M_n)` a tower of `A`-modules with
`I^{N+n} M_n = 0` for every `n`. Then `lim_n M_n` is a retract of its own `I`-adic completion, and
hence `I`-adically complete; at `N = 0` this is `invLimit_isAdicComplete`. For the `p`-adic ideal
of a ring `D` this gives item (07JB) of [Stacks, Tag 07JG] for a tower of `D`-modules whose level
`n` is annihilated by `p^{N+n}`.

## Main definitions

* `Crystalline.shiftedLevelProjQ`: the projection `lim_n M_n → M_k` read on the `(N+k)`-th
  quotient of `lim_n M_n`.
* `Crystalline.shiftedLevelEval`: that map composed with the completion's evaluation at `N + k`.
* `Crystalline.shiftedLevelRetract`: the retraction `(lim_n M_n)^∧ → lim_n M_n`.

## Main results

* `Crystalline.shiftedLevelRetract_of`: the retraction is a left inverse of the canonical map to
  the completion.
* `Crystalline.invLimit_isAdicComplete_of_shift`: for a finitely generated `I` and a tower with
  `I^{N+n} M_n = 0`, the limit `lim_n M_n` is `I`-adically complete.
* `Crystalline.isPAdicallyComplete_invLimit_of_shift`: the limit of a tower of `D`-modules whose
  level `n` is annihilated by `p^{N+n}` is a `p`-adically complete `D`-module.
* `Crystalline.pAdicIdeal_pow_smul_top_eq_bot_iff`: the level `n` is annihilated by the
  `(N+n)`-th power of the `p`-adic ideal exactly when `p^{N+n}` kills each of its elements.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 0G1Q](https://stacks.math.columbia.edu/tag/0G1Q)
-/

@[expose] public section

universe u w

namespace Crystalline

/-! ### The shifted retraction of a limit off its completion -/

section Shift

variable {A : Type u} [CommRing A] (I : Ideal A) (M : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)] (t : ∀ n, M (n + 1) →ₗ[A] M n) (N : ℕ)
  (hM : ∀ n, I ^ (N + n) • (⊤ : Submodule A (M n)) = ⊥)

include hM

/-- **The projection to level `k` kills `I^{N+k} (lim_n M_n)`.** -/
theorem shiftedLevel_pow_smul_top_le_ker (k : ℕ) :
    I ^ (N + k) • (⊤ : Submodule A (invLimit M t)) ≤
      LinearMap.ker (invLimit.proj M t k) := by
  rw [LinearMap.ker, ← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact (Submodule.smul_mono le_rfl le_top).trans (hM k).le

/-- **The projection to level `k`, read on the `(N+k)`-th quotient of the limit.** -/
noncomputable def shiftedLevelProjQ (k : ℕ) :
    (invLimit M t ⧸ (I ^ (N + k) • (⊤ : Submodule A (invLimit M t)))) →ₗ[A] M k :=
  Submodule.liftQ _ (invLimit.proj M t k) (shiftedLevel_pow_smul_top_le_ker I M t N hM k)

/-- `Crystalline.shiftedLevelProjQ` sends the class of `x` to the level-`k` projection of `x`. -/
@[simp] theorem shiftedLevelProjQ_mk (k : ℕ) (x : invLimit M t) :
    shiftedLevelProjQ I M t N hM k (Submodule.Quotient.mk x) = invLimit.proj M t k x :=
  rfl

/-- **The `k`-th evaluation `(lim_n M_n)^∧ → M_k`**, the completion evaluated at level `N + k`
followed by the projection of `Crystalline.shiftedLevelProjQ`. -/
noncomputable def shiftedLevelEval (k : ℕ) :
    AdicCompletion I (invLimit M t) →ₗ[A] M k :=
  (shiftedLevelProjQ I M t N hM k).comp
    (AdicCompletion.eval I (invLimit M t) (N + k))

/-- `Crystalline.shiftedLevelEval` sends the image of `x` in the completion to the level-`k`
projection of `x`. -/
@[simp] theorem shiftedLevelEval_of (k : ℕ) (x : invLimit M t) :
    shiftedLevelEval I M t N hM k (AdicCompletion.of I (invLimit M t) x) =
      invLimit.proj M t k x := by
  simp [shiftedLevelEval]

/-- **The evaluations are compatible with the transition maps of the tower.** -/
theorem shiftedLevelEval_compat (k : ℕ) (y : AdicCompletion I (invLimit M t)) :
    t k (shiftedLevelEval I M t N hM (k + 1) y) = shiftedLevelEval I M t N hM k y := by
  have hle : N + k ≤ N + (k + 1) := by omega
  have hev : AdicCompletion.transitionMap I (invLimit M t) hle
      (AdicCompletion.eval I (invLimit M t) (N + (k + 1)) y) =
      AdicCompletion.eval I (invLimit M t) (N + k) y := by
    rw [← LinearMap.comp_apply, AdicCompletion.transitionMap_comp_eval]
  have hbar : ∀ c : invLimit M t ⧸ (I ^ (N + (k + 1)) • (⊤ : Submodule A (invLimit M t))),
      t k (shiftedLevelProjQ I M t N hM (k + 1) c) =
        shiftedLevelProjQ I M t N hM k
          (AdicCompletion.transitionMap I (invLimit M t) hle c) := fun c =>
    Submodule.Quotient.induction_on _ c (invLimit.proj_comp_transition M t k)
  exact (hbar _).trans (congrArg _ hev)

/-- **The retraction `(lim_n M_n)^∧ → lim_n M_n`**, whose `k`-th component is
`Crystalline.shiftedLevelEval`. -/
noncomputable def shiftedLevelRetract :
    AdicCompletion I (invLimit M t) →ₗ[A] invLimit M t :=
  LinearMap.codRestrict (invLimit M t)
    (LinearMap.pi fun k ↦ shiftedLevelEval I M t N hM k)
    fun y k ↦ shiftedLevelEval_compat I M t N hM k y

/-- **The retraction is a left inverse of the canonical map to the completion.** -/
theorem shiftedLevelRetract_of (x : invLimit M t) :
    shiftedLevelRetract I M t N hM (AdicCompletion.of I (invLimit M t) x) = x :=
  Subtype.ext <| funext fun k ↦ shiftedLevelEval_of I M t N hM k x

/-- For a finitely generated ideal `I` and a tower `(M_n)` of `A`-modules with `I^{N+n} M_n = 0`
for all `n`, the limit `lim_n M_n` is `I`-adically complete. -/
theorem invLimit_isAdicComplete_of_shift (hI : I.FG) :
    IsAdicComplete I (invLimit M t) :=
  Stacks.Examples.isAdicComplete_of_retraction
    (AdicCompletion.of I (invLimit M t)) (shiftedLevelRetract I M t N hM)
    (LinearMap.ext (shiftedLevelRetract_of I M t N hM))
    (AdicCompletion.isAdicComplete hI)

end Shift

/-! ### `p`-adic completeness -/

section PAdic

variable (p : ℕ) (D : Type u) [CommRing D] (M : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module D (M n)] (t : ∀ n, M (n + 1) →ₗ[D] M n) (N : ℕ)

/-- The limit of a tower of `D`-modules whose level `n` is annihilated by `p^{N+n}` is a
`p`-adically complete `D`-module. -/
theorem isPAdicallyComplete_invLimit_of_shift
    (hM : ∀ n, DividedPowers.pAdicIdeal (A := D) p ^ (N + n) •
      (⊤ : Submodule D (M n)) = ⊥) :
    IsPAdicallyComplete p D (invLimit M t) :=
  invLimit_isAdicComplete_of_shift (DividedPowers.pAdicIdeal (A := D) p) M t N hM
    (Submodule.fg_span_singleton _)

/-- The level `n` is annihilated by the `(N+n)`-th power of the `p`-adic ideal exactly when
`p^{N+n}` kills every one of its elements. -/
theorem pAdicIdeal_pow_smul_top_eq_bot_iff {n : ℕ} :
    DividedPowers.pAdicIdeal (A := D) p ^ (N + n) • (⊤ : Submodule D (M n)) = ⊥ ↔
      ∀ x : M n, ((p : D) ^ (N + n)) • x = 0 := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    eq_bot_iff]
  refine ⟨fun h x ↦ ?_, fun h y hy ↦ ?_⟩
  · exact h (Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨x, trivial, rfl⟩)
  · obtain ⟨x, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    rw [Submodule.mem_bot]
    exact h x

end PAdic

end Crystalline

end
