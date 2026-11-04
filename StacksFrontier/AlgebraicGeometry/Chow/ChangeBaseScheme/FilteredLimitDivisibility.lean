module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension

/-!
# Divisibility of a Chow class descends to a finite stage

[Stacks, Tag 0FVQ] presents `CH_k(X')` over a limit base as the colimit of the `CH_k(X_i)` over
the stages: every class over the limit comes from a stage
(`Stacks.Chow.FilteredBaseChangeSystem.exists_stageChowPullback_eq`) and a class killed over the
limit is killed by some transition
(`Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_zero`). Those are the
two halves of a colimit, and what a descent argument actually needs is the statement they give
for one *equation*: if the image of a stage class over the limit is divisible by `n`, then the
image of that class at some later stage is already divisible by `n`.

This is the first reduction of [Stacks, Tag 0FH7] — "let `k'` be a separable algebraic closure
of `k`; suppose the pullback of `[x] - [x']` to `X_{k'}` is divisible by `n`; then we conclude by
[Stacks, Tag 0FH6]" — with the geometry stripped out: it holds for divisibility by any integer,
in any degree, for any `Stacks.Chow.FilteredBaseChangeSystem`.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_nsmul`: if
  `stageChowPullback j β = n • γ` over the limit, then `transitionChowPullback f β = n • δ` at
  some stage `i ⟶ j`.

## Implementation notes

The witness `γ` over the limit need not itself come from the stage `j`; it comes from some stage
`a` by the surjectivity half of [Stacks, Tag 0FVQ], and `j` and `a` are then met at
`CategoryTheory.IsCofiltered.min`. There the difference
`transition β - n • transition (witness)` is a class whose image over the limit vanishes, and the
eventual-injectivity half of [Stacks, Tag 0FVQ] kills it at a further stage. Composing the two
transitions with `Stacks.Chow.FilteredBaseChangeSystem.transitionChowPullback_comp` presents the
result at a single transition out of `j`.

No `@[stacks 0FVQ]` attribute is carried: the tag's two halves are the surjectivity and the
eventual injectivity, both already registered in
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitChow`, and this is a
consequence of them.

## References

* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Chow.FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-- **Divisibility over the limit base descends to a stage.** Let `β` be a `k`-cycle class on the
stage `X_j` whose image on `X'` is `n` times a class `γ` of `CH_k(X')`. Then there is a transition
`i ⟶ j` and a class `δ` on `X_i` with the image of `β` on `X_i` equal to `n • δ`.

Both halves of [Stacks, Tag 0FVQ] are used: `γ` comes from some stage `a`, and after meeting `j`
and `a` the difference between the two readings of the equation is a class vanishing over the
limit, hence killed by a further transition. -/
theorem exists_transitionChowPullback_eq_nsmul (j : I) (k : ℤ) (n : ℤ)
    (β : chowGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k)
    (γ : chowGroup s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k)
    (hβ : s.stageChowPullback j k β = n • γ) :
    ∃ (i : I) (f : i ⟶ j)
      (δ : chowGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k),
      s.transitionChowPullback f k β = n • δ := by
  obtain ⟨a, w, hw⟩ := s.exists_stageChowPullback_eq k γ
  set m : I := IsCofiltered.min j a with hm
  set f₁ : m ⟶ j := IsCofiltered.minToLeft j a with hf₁
  set f₂ : m ⟶ a := IsCofiltered.minToRight j a with hf₂
  set ε : chowGroup (s.stageSituation m) (pullback.snd s.X.hom (s.stageToBase m)) k :=
    s.transitionChowPullback f₁ k β - n • s.transitionChowPullback f₂ k w with hε
  have hvanish : s.stageChowPullback m k ε = 0 := by
    rw [hε, map_sub, map_zsmul, s.stageChowPullback_transitionChowPullback f₁ k β,
      s.stageChowPullback_transitionChowPullback f₂ k w, hβ, hw, sub_self]
  obtain ⟨i, t, ht⟩ := s.exists_transitionChowPullback_eq_zero m k ε hvanish
  refine ⟨i, t ≫ f₁, s.transitionChowPullback (t ≫ f₂) k w, ?_⟩
  rw [hε, map_sub, map_zsmul, sub_eq_zero] at ht
  rw [← s.transitionChowPullback_comp t f₁ k β, ht,
    ← s.transitionChowPullback_comp t f₂ k w]

end Stacks.Chow.FilteredBaseChangeSystem

end
