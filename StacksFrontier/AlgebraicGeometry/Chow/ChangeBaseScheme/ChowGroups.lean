module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles

/-!
# Chow groups under a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c`, that is a flat
morphism `g : S' ⟶ S` of the two bases whose dimension functions differ by `c` on the generic
points of the fibres of `g`, and let `X` be locally of finite type over `S` with base change
`X' = X ×_S S'`. `Stacks.Chow.baseChangeCyclePullback` is the induced homomorphism
`Z_k(X) ⟶ Z_{k+c}(X')` on cycle groups. This file descends it to Chow groups,
`A_k(X) ⟶ A_{k+c}(X')`, granted that it carries cycles rationally equivalent to zero to cycles
rationally equivalent to zero.

## Main definitions

* `Stacks.Chow.BaseChangeFactorsThroughRationalEquivalence` — Stacks 0FVJ, that base change of
  cycles preserves rational equivalence, read as a hypothesis.
* `Stacks.Chow.flatBaseChangeChowPullback` — the homomorphism `A_k(X) ⟶ A_{k+c}(X')` of Chow
  groups.

## Main results

* `Stacks.Chow.flatBaseChangeChowPullback_mk` — on the class of a cycle, the map is the class of
  the base change of that cycle.

## Implementation notes

Stacks 0FVJ, that the base change of a cycle rationally equivalent to zero is again rationally
equivalent to zero, is not formalized in this repository, and is carried as the explicit
hypothesis `Stacks.Chow.BaseChangeFactorsThroughRationalEquivalence`. This is the convention of
`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`, which carries Stacks 02S1 the same
way: the hypothesis *is* the existence of the map, so nothing is lost by taking it as a
parameter, and no `@[stacks 0FVJ]` attribute is placed on a declaration that carries it.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks 0FVJ.** The assertion that the base change of `k`-cycles along a flat change of the
base scheme carries cycles rationally equivalent to zero to cycles rationally equivalent to
zero, hence factors through rational equivalence.

Carried as a hypothesis, because Stacks 0FVJ is not formalized in this repository; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowGroups`. -/
def BaseChangeFactorsThroughRationalEquivalence (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ) : Prop :=
  ∀ α ∈ rationalEquivalences B.base f k,
    baseChangeCyclePullback B f k α ∈
      rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c)

/-- The homomorphism `A_k(X) ⟶ A_{k+c}(X ×_S S')` of Chow groups induced by a flat change of the
base scheme with dimension shift `c`, granted that base change of cycles factors through
rational equivalence. -/
def flatBaseChangeChowPullback (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (hfac : BaseChangeFactorsThroughRationalEquivalence B f k) :
    chowGroup B.base f k →+ chowGroup B.baseChange (pullback.snd f B.g) (k + B.c) :=
  QuotientAddGroup.map (rationalEquivalences B.base f k)
    (rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c))
    (baseChangeCyclePullback B f k) fun α hα ↦ hfac α hα

/-- On the class of a cycle, base change on Chow groups is the class of the base change of that
cycle. -/
@[simp]
theorem flatBaseChangeChowPullback_mk (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (hfac : BaseChangeFactorsThroughRationalEquivalence B f k) (α : CycleGroup B.base f k) :
    flatBaseChangeChowPullback B f k hfac
        (QuotientAddGroup.mk' (rationalEquivalences B.base f k) α) =
      QuotientAddGroup.mk'
        (rationalEquivalences B.baseChange (pullback.snd f B.g) (k + B.c))
        (baseChangeCyclePullback B f k α) :=
  rfl

end Stacks.Chow

end
