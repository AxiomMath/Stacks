module

public import Mathlib.RingTheory.Localization.Away.Lemmas
import StacksCore.Tactic.StacksAttribute

/-! # Localizing away from an idempotent

For an idempotent `e` of a commutative ring `R`, the quotient `R ⧸ (e)` is the localization of `R`
away from the complementary idempotent `1 - e`.
-/

-- Mathlib states this in the complementary orientation, `Away e (R ⧸ (1 - e))`. Since it is
-- quantified over every idempotent and `e ↦ 1 - e` is an involution on idempotents, that is the
-- same theorem with the letters exchanged.
add_to_stacks 00EH "(2)" IsLocalization.Away.quotient_of_isIdempotentElem

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **Stacks 00EH**, clause (2), in the tag's orientation: for an idempotent `e`, the quotient
`R ⧸ (e)` is the localization of `R` away from `1 - e`.

This is `IsLocalization.Away.quotient_of_isIdempotentElem` with `e` replaced by `1 - e`, but that
substitution cannot be performed by rewriting: the offending `1 - (1 - e)` occurs as a *type index*
of the quotient, so `simp` and `▸` both fail on the motive. Going through
`IsLocalization.away_of_isIdempotentElem` instead puts the kernel equation in hypothesis position,
where `simp` reaches it. -/
@[stacks 00EH "(2)"]
theorem IsLocalization.Away.quotient_span_singleton_of_isIdempotentElem {e : R}
    (he : IsIdempotentElem e) : IsLocalization.Away (1 - e) (R ⧸ Ideal.span {e}) :=
  IsLocalization.away_of_isIdempotentElem he.one_sub (by simp) Ideal.Quotient.mk_surjective

/-- **Stacks 00EH**, clause (2), as the isomorphism the tag states. Mathlib carries only the
`IsLocalization.Away` predicate, never a bundled map, so this records `R ⧸ (e) ≅ R_{1 - e}`. -/
@[stacks 00EH "(2)"]
noncomputable def IsLocalization.Away.quotientAlgEquiv {e : R} (he : IsIdempotentElem e) :
    (R ⧸ Ideal.span {e}) ≃ₐ[R] Localization.Away (1 - e) :=
  letI := IsLocalization.Away.quotient_span_singleton_of_isIdempotentElem he
  IsLocalization.algEquiv (Submonoid.powers (1 - e)) _ _
