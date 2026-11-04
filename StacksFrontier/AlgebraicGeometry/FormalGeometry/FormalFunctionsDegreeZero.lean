module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Completeness of an extension by a module killed by a power of the ideal

Let `R` be a commutative ring, `I ⊆ R` an ideal and `N` an `R`-module with a submodule `M` such
that `IᶜN ⊆ M` for some `c`, i.e. such that `N / M` is annihilated by a power of `I`. If `M` is
`I`-adically complete then so is `N`.

This is the algebraic input of Stacks 0EII (formal functions in degree zero) that is not already
in the library. There the module `N` is `Γ(U, M̃)` for `U = Spec(A) ∖ V(𝔞)`, the submodule is the
image of `M / H⁰_𝔞(M)` — a finite module over a complete ring, hence complete by
`Stacks.isAdicComplete_of_iInf_smul_eq_bot` — and the quotient is `H¹_𝔞(M)`, which the hypotheses
of 0EII assume to be annihilated by a power of `f`. Stacks deduces completeness of `N` from
Algebra, Lemma 0BNG; the argument below is the same one, carried out directly on the Hausdorff and
precompleteness conditions instead of through the completed short exact sequence, since that is
all 0EII uses.

The two filtrations are compared by `Iᶜ⁺ⁿN ⊆ IⁿM ⊆ M ∩ IⁿN`, so a sequence that is Cauchy in `N`
becomes Cauchy in `M` after shifting its index by `c` and subtracting its `c`-th term, and a limit
in `M` of that shifted sequence is a limit in `N` of the original one.

## Main results

* `Stacks.Algebraization.smul_top_le_smul_of_pow_smul_top_le` — the comparison of filtrations.
* `Stacks.Algebraization.isHausdorff_of_pow_smul_top_le` — the Hausdorff half.
* `Stacks.Algebraization.isPrecomplete_of_pow_smul_top_le` — the precompleteness half.
* `Stacks.Algebraization.isAdicComplete_of_pow_smul_top_le` — **the result**: `N` is
  `I`-adically complete.
* `Stacks.Algebraization.pow_span_singleton_smul_top_le` — the hypothesis in the shape Stacks
  0EII supplies it, namely that `N / M` is annihilated by `f ^ c`.

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0BNG](https://stacks.math.columbia.edu/tag/0BNG)
-/

@[expose] public section

universe u v

namespace Stacks.Algebraization

variable {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]

/-- **The comparison of filtrations.** If `IᶜN ⊆ M`, then `Iᶜ⁺ⁿN` is contained in `IⁿM`. -/
theorem smul_top_le_smul_of_pow_smul_top_le {I : Ideal R} {M : Submodule R N} {c : ℕ}
    (hc : I ^ c • (⊤ : Submodule R N) ≤ M) (n : ℕ) :
    I ^ (n + c) • (⊤ : Submodule R N) ≤ I ^ n • M := by
  rw [pow_add, Submodule.mul_smul]
  exact smul_mono_right _ hc

/-- If `M` is `I`-adically separated and `N / M` is annihilated by `Iᶜ`, then `N` is
`I`-adically separated. -/
theorem isHausdorff_of_pow_smul_top_le (I : Ideal R) (M : Submodule R N) (c : ℕ)
    (hc : I ^ c • (⊤ : Submodule R N) ≤ M) (hM : IsHausdorff I M) :
    IsHausdorff I N := by
  refine ⟨fun x hx ↦ ?_⟩
  have hmem : ∀ n : ℕ, x ∈ I ^ n • (⊤ : Submodule R N) := by
    intro n
    simpa using (SModEq.sub_mem).mp (hx n)
  have hxM : x ∈ M := hc (by simpa using hmem c)
  have := hM.haus ⟨x, hxM⟩ fun n ↦ by
    refine (SModEq.sub_mem).mpr ?_
    simpa using (Submodule.mem_smul_top_iff (I ^ n) M ⟨x, hxM⟩).mpr
      (smul_top_le_smul_of_pow_smul_top_le hc n (hmem (n + c)))
  simpa using congrArg (Subtype.val) this

/-- If `M` is `I`-adically precomplete and `N / M` is annihilated by `Iᶜ`, then `N` is
`I`-adically precomplete.

A Cauchy sequence `f` in `N` has all its differences `f (n + c) - f c` inside `M`, and the
sequence of those differences is Cauchy in `M`; adding `f c` to its limit gives a limit of `f`. -/
theorem isPrecomplete_of_pow_smul_top_le (I : Ideal R) (M : Submodule R N) (c : ℕ)
    (hc : I ^ c • (⊤ : Submodule R N) ≤ M) (hM : IsPrecomplete I M) :
    IsPrecomplete I N := by
  refine ⟨fun f hf ↦ ?_⟩
  -- The differences of `f` past index `c` lie in `M`.
  have hdiff : ∀ m n : ℕ, m ≤ n → f m - f n ∈ I ^ m • (⊤ : Submodule R N) := by
    intro m n hmn
    simpa using (SModEq.sub_mem).mp (hf hmn)
  set g : ℕ → M := fun n ↦
    ⟨f (n + c) - f c, hc (sub_mem_comm_iff.mp (hdiff c (n + c) (Nat.le_add_left c n)))⟩
    with hg
  -- That sequence is Cauchy in `M`.
  obtain ⟨L, hL⟩ := hM.prec (f := g) fun {m n} hmn ↦ by
    refine (SModEq.sub_mem).mpr ?_
    rw [Submodule.mem_smul_top_iff]
    have := hdiff (m + c) (n + c) (Nat.add_le_add_right hmn c)
    have hsub : ((g m : N) - (g n : N)) = f (m + c) - f (n + c) := by
      simp only [hg]
      abel
    simpa [AddSubgroupClass.coe_sub, hsub] using
      smul_top_le_smul_of_pow_smul_top_le hc m this
  -- Its limit, translated back, is a limit of `f`.
  refine ⟨f c + (L : N), fun n ↦ (SModEq.sub_mem).mpr ?_⟩
  have h₁ := hdiff n (n + c) (Nat.le_add_right n c)
  have h₂ : (g n : N) - (L : N) ∈ I ^ n • (⊤ : Submodule R N) := by
    have hmem := (Submodule.mem_smul_top_iff (I ^ n) M (g n - L)).mp
      ((SModEq.sub_mem).mp (hL n))
    simpa using (smul_mono_right (I ^ n) (le_top : M ≤ ⊤)) hmem
  have hrw : f n - (f c + (L : N)) = (f n - f (n + c)) + ((g n : N) - (L : N)) := by
    simp only [hg]
    abel
  rw [hrw]
  exact Submodule.add_mem _ h₁ h₂

/-- **Completeness of an extension by a module killed by a power of the ideal.** If `M ⊆ N` is
`I`-adically complete and `IᶜN ⊆ M`, so that `N / M` is annihilated by `Iᶜ`, then `N` is
`I`-adically complete.

This is the step of Stacks 0EII that deduces completeness of `Γ(U, M̃)` from completeness of
`M / H⁰_𝔞(M)` and the annihilation of `H¹_𝔞(M)` by a power of `f`. -/
theorem isAdicComplete_of_pow_smul_top_le (I : Ideal R) (M : Submodule R N) (c : ℕ)
    (hc : I ^ c • (⊤ : Submodule R N) ≤ M) (hM : IsAdicComplete I M) :
    IsAdicComplete I N where
  __ := isHausdorff_of_pow_smul_top_le I M c hc hM.toIsHausdorff
  __ := isPrecomplete_of_pow_smul_top_le I M c hc hM.toIsPrecomplete

/-- The hypothesis of `Stacks.Algebraization.isAdicComplete_of_pow_smul_top_le` in the form the
hypotheses of Stacks 0EII supply it: the quotient `N / M` is annihilated by `f ^ c`. -/
theorem pow_span_singleton_smul_top_le (f : R) (M : Submodule R N) (c : ℕ)
    (h : ∀ x : N ⧸ M, f ^ c • x = 0) :
    (Ideal.span {f}) ^ c • (⊤ : Submodule R N) ≤ M := by
  rw [Ideal.span_singleton_pow, Submodule.smul_le]
  intro a ha x _
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
  have hx : (Submodule.Quotient.mk (f ^ c • (b • x)) : N ⧸ M) = 0 := by
    rw [← Submodule.mkQ_apply, map_smul, Submodule.mkQ_apply]
    exact h _
  simpa [mul_smul] using (Submodule.Quotient.mk_eq_zero M).mp hx

end Stacks.Algebraization

end
