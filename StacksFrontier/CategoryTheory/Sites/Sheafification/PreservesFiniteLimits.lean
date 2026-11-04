module

public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification preserves finite limits

Let `(C, J)` be a site and let `A` be a concrete category in which the plus construction `F ↦ F^+`
can be carried out: `A` has the multiequalizers and the colimits over the categories of coverings
out of which `F^+` is built, and `forget A` preserves those colimits and reflects isomorphisms.
Then the inclusion of sheaves into presheaves has a left adjoint, sheafification `PSh(C) ⥤ Sh(C)`,
`F ↦ F^#`. Stacks 00WJ says that `F ↦ F^#` is exact, and the half proved here is the one that is
not formal: that it commutes with finite limits.

The colimits in the construction of `F^+` are over the coverings of an object ordered by
refinement, which is a directed set (Stacks 00W6, 00W7), and a filtered colimit of sets commutes
with a finite limit (Stacks 002W). So `F ↦ F^+` commutes with finite limits of presheaves as soon
as the finite limits of `A` and those filtered colimits are both computed on underlying sets; and
limits of sheaves are limits of presheaves (Stacks 00W2), so the presheaf-level statement transfers
to `F ↦ F^#`. Those are exactly the hypotheses below.

## Main results

* `presheafToSheaf_preservesFiniteLimits`: Stacks 00WJ, left-exact half — sheafification
  `presheafToSheaf J A : PSh(C) ⥤ Sh(C)`, `F ↦ F^#`, preserves finite limits, for sheaves with
  values in a concrete category `A` whose finite limits and coverings colimits are computed on
  underlying sets.

## Implementation notes

* Exactness of a functor between categories that are not additive means, in the source (Categories,
  Definition 0034), commuting with finite limits and with finite colimits, so Stacks 00WJ is the
  conjunction of two assertions about `F ↦ F^#`. They are not stated together, because they hold
  under different hypotheses and a conjunction would impose the union: the finite colimits half is
  formal — a left adjoint preserves all colimits, Categories, Lemma 0039 — and therefore holds for
  sheaves with values in *any* category for which sheafification exists, where it is
  `CategoryTheory.presheafToSheaf_preservesFiniteColimits`. Only the finite limits half needs the
  construction of `F^+`, and that half is what is stated here; the two together are the tag.
* Mathlib's `CategoryTheory.HasSheafify J A` *is* the assertion that the inclusion admits a left
  exact left adjoint, so assuming it would make this conclusion a hypothesis. The hypotheses
  assumed instead are the ones the source's proof uses, namely those under which `F^+` is a
  filtered colimit computed on underlying sets. Mathlib proves the presheaf-level half at exactly
  these hypotheses (`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification`),
  but its two sheaf-level forms — `CategoryTheory.preservesFiniteLimits_presheafToSheaf`, for the
  plus construction `CategoryTheory.plusPlusSheaf J A` itself, and the `HasSheafify` instance
  deduced from it — both require `PreservesLimits (forget A)`, preservation of *all* limits, which
  the argument does not use; only finite ones are required here, so that the statement applies to a
  concrete category whose forgetful functor is merely left exact.
* Sheaves of sets, which is what the source's section is about, are the case `A = Type max u v` for
  a site `C : Type u` with `Category.{v} C`, and there every hypothesis is automatic: `forget A` is
  isomorphic to the identity functor, so it preserves the coverings colimits and the multiequalizer
  limits and reflects isomorphisms; `Type max u v` has limits and colimits of every shape at its
  own level, which is the level of `J.Cover X` and of the multicospans; and the smallness asked for
  is `Small.{max u v, max u v}`, which every type has. The conclusion is then the source's
  statement.
* The functor is Mathlib's chosen left adjoint `CategoryTheory.presheafToSheaf J A` rather than an
  arbitrary one. Nothing is lost: a left adjoint of `sheafToPresheaf J A` is unique up to unique
  isomorphism (`CategoryTheory.Adjunction.leftAdjointUniq`) — the characterization of `F ↦ F^#` the
  source gives after Theorem 00WB — and preserving finite limits is invariant under isomorphism of
  functors.

## References

* [Stacks 00WJ](https://stacks.math.columbia.edu/tag/00WJ), whose proof of this half is Categories,
  Lemma 002W — a filtered colimit of sets commutes with a finite limit — applied to the colimits
  defining `F ↦ F^+`.
-/

@[expose] public section

universe t w v u

open CategoryTheory Limits

/-- **Stacks 00WJ**, left-exact half. Let `(C, J)` be a site and let `A` be a concrete category in
which the plus construction `F ↦ F^+` can be carried out and whose finite limits and coverings
colimits are computed on underlying sets. Then sheafification
`presheafToSheaf J A : PSh(C) ⥤ Sh(C)`, `F ↦ F^#`, preserves finite limits. Together with
`CategoryTheory.presheafToSheaf_preservesFiniteColimits`, which holds because `F ↦ F^#` is a left
adjoint, this says that sheafification is exact. -/
@[stacks 00WJ "Sheafification `PSh(C) → Sh(C)`, `F ↦ F^#`, is exact: it commutes with finite limits
  and with finite colimits. This is the left-exact half; the right-exact half is
  `CategoryTheory.presheafToSheaf_preservesFiniteColimits`.",
  sga "3 IV 4.3.16" "partial",
  sga "3 IV 4.4.1" "more general",
  sga "4 II 3.4" "more general",
  sga "4 II 4.1" "Clause 1",
  sga "4 II 6.3.3" "more general"]
public theorem presheafToSheaf_preservesFiniteLimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type w) [Category.{t} A]
    {FA : A → A → Type*} {CA : A → Type t} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{t} A FA]
    [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)]
    [∀ {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget A)]
    [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ]
    [(forget A).ReflectsIsomorphisms] [HasFiniteLimits A] [PreservesFiniteLimits (forget A)] :
    PreservesFiniteLimits (presheafToSheaf J A) :=
  -- `F ↦ F^+` commutes with finite limits of presheaves (Stacks 00W6, 00W7 and Categories, Lemma
  -- 002W), and `F ↦ F^#` followed by the inclusion is that construction.
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙ sheafToPresheaf J A) :=
    preservesFiniteLimits_of_natIso (plusPlusFunctorIsoSheafification J A)
  -- Limits of sheaves are limits of presheaves (Stacks 00W2): `sheafToPresheaf` reflects limits.
  preservesFiniteLimits_of_reflects_of_preserves (presheafToSheaf J A) (sheafToPresheaf J A)
