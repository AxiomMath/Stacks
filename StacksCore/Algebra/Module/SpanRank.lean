module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # A map out of a free module of too big rank has a nonzero kernel

Stacks 05WI. `Mathlib.LinearAlgebra.FreeModule.StrongRankCondition` is imported for
`commRing_strongRankCondition`, which supplies `StrongRankCondition R` from the tag's own
hypothesis that `R` is a nonzero commutative ring; without it these lemmas do not apply at a
concrete ring such as `ℤ`.
-/

@[expose] public section

open Cardinal Submodule

namespace Module

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If the rank of `M` is smaller than `n`, then no `R`-linear map `Rⁿ → M` is injective. -/
theorem not_injective_of_rank_lt [Nontrivial R] {n : ℕ} (h : Module.rank R M < n)
    (f : (Fin n → R) →ₗ[R] M) : ¬ Function.Injective f := fun hf =>
  h.not_ge (Module.le_rank_iff_exists_linearMap.2 ⟨f, hf⟩)

/-- **Stacks 05WI**, in its general form: no nontriviality or `Ring` hypothesis, and stated as
non-injectivity rather than as a nonzero kernel. -/
@[stacks 05WI]
theorem not_injective_of_spanRank_lt [StrongRankCondition R] {n : ℕ}
    (h : (⊤ : Submodule R M).spanRank < n) (f : (Fin n → R) →ₗ[R] M) :
    ¬ Function.Injective f :=
  have := nontrivial_of_invariantBasisNumber R
  not_injective_of_rank_lt (Submodule.rank_le_spanRank.trans_lt h) f

/-- If `M` is spanned by a set of cardinality `< n`, no `R`-linear map `Rⁿ → M` is injective. -/
theorem not_injective_of_span_eq_top_of_mk_lt [StrongRankCondition R] {n : ℕ} {s : Set M}
    (hs : Submodule.span R s = ⊤) (hlt : #s < n) (f : (Fin n → R) →ₗ[R] M) :
    ¬ Function.Injective f :=
  not_injective_of_spanRank_lt (by rw [← hs]; exact (spanRank_span_le_card s).trans_lt hlt) f

end Module

section Ring

variable {R M : Type*} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]

/-- **Stacks 05WI** in the tag's literal wording: the kernel is nonzero. The tag's `n ≥ 1` is
implied by `spanRank ⊤ < n`, and `Module.Finite M` is not needed. -/
@[stacks 05WI]
theorem LinearMap.ker_ne_bot_of_spanRank_lt {n : ℕ}
    (h : (⊤ : Submodule R M).spanRank < n) (f : (Fin n → R) →ₗ[R] M) : LinearMap.ker f ≠ ⊥ :=
  fun hk => Module.not_injective_of_spanRank_lt h f (LinearMap.ker_eq_bot.1 hk)

/-- The form a consumer usually has to hand: `M` spanned by a finite set of size `< n`. -/
theorem LinearMap.ker_ne_bot_of_span_finset_card_lt {n : ℕ} {s : Finset M}
    (hs : Submodule.span R (s : Set M) = ⊤) (hlt : s.card < n) (f : (Fin n → R) →ₗ[R] M) :
    LinearMap.ker f ≠ ⊥ := fun hk =>
  Module.not_injective_of_span_eq_top_of_mk_lt hs (by simpa using hlt) f (LinearMap.ker_eq_bot.1 hk)

end Ring

