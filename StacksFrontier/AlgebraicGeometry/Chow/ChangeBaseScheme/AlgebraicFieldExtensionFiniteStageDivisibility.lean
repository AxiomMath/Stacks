module

public import Mathlib.FieldTheory.SeparableClosure
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionFiniteStage
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitDivisibility

/-!
# Descending the divisibility of a Chow class to a finite subextension

Let `K/k` be an algebraic extension of fields and let `X` be a quasi-compact scheme of finite
type over `k`. If the base change to `X_K` of a `k`-cycle class on `X` is divisible by an integer
`n` in `CH_i(X_K)`, then its base change to `X_{k'}` is already divisible by `n` for some finite
subextension `K/k'/k`.

This is the first reduction of [Stacks, Tag 0FH7]: that proof takes `k'` to be a separable
algebraic closure of `k`, produces there a class `γ` with `n γ` the pullback of `[x] - [x']`, and
then descends to a finite separable subextension "by [Stacks, Tag 0FH6]". The descent itself has
nothing to do with the two points, with smoothness, or with separability; it is the statement
below, for an arbitrary algebraic extension, an arbitrary integer and an arbitrary degree.

## Main results

* `Stacks.Chow.exists_finiteSubextension_baseChangeChowPullback_eq_zsmul` — divisibility of a
  Chow class by `n` after an algebraic base change is already achieved over a finite
  subextension.
* `Stacks.Chow.exists_finiteSeparable_baseChangeChowPullback_eq_zsmul` — the same at the
  separable closure, with the stage presented as a finite separable extension: **step 1 of
  [Stacks, Tag 0FH7]** in the shape that proof's conclusion asks for.

## Implementation notes

The two halves of [Stacks, Tag 0FH6] enter through
`Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_nsmul`, which is the
colimit presentation of `CH_i(X_K)` applied to one equation, and the identification of the base
change from `k` with the stage and transition comparison homomorphisms of
`Stacks.Chow.algebraicExtensionSystem` is
`Stacks.Chow.stageChowPullback_baseChangeChowPullback` and
`Stacks.Chow.transitionChowPullback_baseChangeChowPullback`. The stage the argument starts from
is the trivial subextension `⊥`, so that the hypothesis over `K` can be read as a statement about
a class coming from a stage; the stage it ends at is the one produced by the descent.

All base changes from `k` are read through the canonical cartesian square of
`CategoryTheory.Limits.pullback`, i.e. through
`Stacks.Chow.baseChangeChowPullbackOfIsPullback` rather than
`Stacks.Chow.baseChangeChowPullback`, which is what the comparison homomorphisms of a
`Stacks.Chow.FilteredBaseChangeSystem` use. Since the dimension shift of a field extension
vanishes this costs no generality, and it keeps every class in the single degree `i` instead of
spreading them over `i` and `i + 0`.

No `@[stacks]` attribute is carried: Tag 0FH6 is registered on
`Stacks.Chow.chowColimitAddEquiv_algebraicExtensionSystem` and Tag 0FH7 asks for much more than
this reduction.

## References

* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

/-- **Divisibility of a Chow class after an algebraic base change descends to a finite
subextension.** Let `K/k` be an algebraic extension of fields, let `X` be a quasi-compact scheme
of finite type over `k`, and let `α` be a `k`-cycle class of dimension `i` on `X` whose base
change to `X_K` is `n` times a class `γ` of `CH_i(X_K)`. Then there is a finite subextension
`K/k'/k` and a class `δ` of `CH_i(X_{k'})` with the base change of `α` to `X_{k'}` equal to
`n δ`.

Note that `γ` is not assumed to come from any finite subextension, and the `δ` produced is not in
general the base change of `γ` to `X_{k'}`.

This is the first reduction of [Stacks, Tag 0FH7], with the geometry stripped out. It rests on
Tag 0FH6 through
`Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_nsmul`. -/
theorem exists_finiteSubextension_baseChangeChowPullback_eq_zsmul
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i n : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i)
    (γ : chowGroup (fieldChowSituation K)
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) i)
    (hα : baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl X.hom
        (IsPullback.of_hasPullback X.hom (fieldExtensionBaseChangeSituation k K).g) i α =
      n • γ) :
    ∃ (E : FiniteSubextension k K) (δ : chowGroup (fieldChowSituation E.1)
        (pullback.snd X.hom (fieldExtensionBaseChangeSituation k E.1).g) i),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k E.1) rfl X.hom
          (IsPullback.of_hasPullback X.hom (fieldExtensionBaseChangeSituation k E.1).g) i α =
        n • δ := by
  let s : FilteredBaseChangeSystem.{u, u, u} (FiniteSubextension k K)ᵒᵖ :=
    algebraicExtensionSystem k K X
  let a₀ : (FiniteSubextension k K)ᵒᵖ := op ⟨⊥, inferInstance⟩
  have hβ : s.stageChowPullback a₀ i
      (baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k a₀.unop.1) rfl
        X.hom (IsPullback.of_hasPullback X.hom
          (fieldExtensionBaseChangeSituation k a₀.unop.1).g) i α) = n • γ :=
    (stageChowPullback_baseChangeChowPullback k K X a₀ i α).trans hα
  obtain ⟨c, f, δ, hδ⟩ := s.exists_transitionChowPullback_eq_nsmul a₀ i n _ γ hβ
  exact ⟨c.unop, δ, (transitionChowPullback_baseChangeChowPullback k K X f i α).symm.trans hδ⟩

/-- **Step 1 of [Stacks, Tag 0FH7].** Let `X` be a quasi-compact scheme of finite type over a
field `k`, and let `α` be a `k`-cycle class of dimension `i` on `X` whose base change to the
separable closure `k^sep` is `n` times a class of `CH_i(X_{k^sep})`. Then there is a **finite
separable** extension `K/k` over which the base change of `α` is already `n` times a class of
`CH_i(X_K)`.

This is `Stacks.Chow.exists_finiteSubextension_baseChangeChowPullback_eq_zsmul` at
`K = k^sep`, with the stage it produces presented as a finite separable extension rather than as
a `Stacks.Chow.FiniteSubextension`. The separability and finiteness of the stage cost nothing:
`k^sep/k` is separable, so instance search proves both of a finite subextension of it, and
`k^sep/k` being algebraic is what lets the preceding theorem apply at all.

It is step 1 of [Stacks, Tag 0FH7] in the shape that proof's conclusion asks for. Everything
specific to 0FH7 — the two rational points, smoothness, projectivity, and the invertibility of
`n` in `k` — is in the production of the class over `k^sep`, not in this descent. -/
theorem exists_finiteSeparable_baseChangeChowPullback_eq_zsmul (k : Type u) [Field k]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i n : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i)
    (γ : chowGroup (fieldChowSituation (SeparableClosure k))
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k (SeparableClosure k)).g) i)
    (hα : baseChangeChowPullbackOfIsPullback
        (fieldExtensionBaseChangeSituation k (SeparableClosure k)) rfl X.hom
        (IsPullback.of_hasPullback X.hom
          (fieldExtensionBaseChangeSituation k (SeparableClosure k)).g) i α =
      n • γ) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : Algebra.IsSeparable k K)
        (δ : chowGroup (fieldChowSituation K)
          (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) i),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl X.hom
          (IsPullback.of_hasPullback X.hom (fieldExtensionBaseChangeSituation k K).g) i α =
        n • δ := by
  obtain ⟨E, δ, hδ⟩ := exists_finiteSubextension_baseChangeChowPullback_eq_zsmul k
    (SeparableClosure k) X i n α γ hα
  exact ⟨E.1, inferInstance, inferInstance, E.2, inferInstance, δ, hδ⟩

end Stacks.Chow

end
