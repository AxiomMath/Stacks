module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension
import StacksCore.Tactic.StacksAttribute

/-!
# All eight assertions for torsion sheaves on curves pass to extensions at once

Let `k` be a field, let `Z` be a scheme over `k` with structure morphism `π`, let `i : Z' ⟶ Z`
be the morphism along which cohomology is restricted, and let `0 → F₁ → F₂ → F₃ → 0` be a short
exact sequence of abelian sheaves on the small étale site of `Z`. Stacks Project Tag 0A5C asserts
that if the eight statements of Situation 0A52 hold for `F₁` and for `F₃`, then they hold for
`F₂`.

This file proves that assertion in its bundled form, for the conjunction
`Stacks.EtaleCohomology.CurveCohomologyStatements` of the eight statements, rather than one
statement at a time.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact_of_constructible_and`:
  the eight statements of Situation 0A52 are closed under extensions.

## Implementation notes

Six of the eight statements already pass to extensions individually, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension`, and
this file does no more than apply those six and supply the two finiteness statements (4) and (5),
which are the unconditional five-lemma statement
`Stacks.EtaleCohomology.finite_sheafCohomology_X₂_of_shortExact` once the side conditions have
been moved to the outer terms of the sequence. The content is therefore the bookkeeping of the
side conditions, and it goes in three different ways:

* the two torsion conditions descend from the middle term to the outer ones outright, by
  `Stacks.EtaleCohomology.isPrimePowerTorsion_of_shortExact` and
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_shortExact`;
* the two conditions on the scheme — affineness of `Z` and properness of `π` — constrain neither
  coefficient sheaf and are passed to the outer terms unchanged;
* constructibility is **not** available: it enters `CurveCohomologyStatements` as an abstract
  predicate, and the source discharges its descent by Proposition 09BH, whose strong form this
  library does not have. It is therefore carried here as the explicit hypothesis
  `hconstructible`, in the one direction the dévissage consumes — from the middle term to the
  outer ones. This is the same treatment the hypothesis receives in
  `Stacks.EtaleCohomology.curveCohomologyStatements_smallEtaleDirectImageAb` (Tag 0A5D), the only
  other result stated at the level of the bundled conjunction.

Statement (8) consumes statement (1) for the sub-sheaf in degree three, not just statement (8)
for the outer terms: a degree-two class on the restricted middle sheaf lifts only modulo the
degree-three cohomology of `F₁`. That dependence is already recorded in the signature of
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing`
and is discharged here from the `vanishing` field of the hypothesis for `F₁`.

No weakening of the source is involved in the quantification: as recorded on
`CurveCohomologyStatements`, the conjunction is stated for an arbitrary morphism `i` and an
arbitrary field, with neither the algebraically closed base nor the separated finite-type scheme
of dimension at most one that Situation 0A52 imposes, so it is stronger than the source's.

This does not close Tag 03SC. Tag 0A5C is one closure property of its dévissage; the base case
(Tags 03SD, 0A3Q, 03SG, 0A5B) is not in this library. The reduction to a dense open (Tag 0GJA)
is, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen`, which
consumes this theorem for one of its two implications.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {Z Z' : Scheme.{u}} (i : Z' ⟶ Z) {k : Type u} [Field k] (π : Z ⟶ Spec (.of k))
  (l p : ℕ)
  {constructible : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **Stacks Project, Tag 0A5C.** The eight statements of Situation 0A52 are closed under
extensions: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of abelian sheaves on the small
étale site of `Z`, if all eight hold for `F₁` and for `F₃` then all eight hold for `F₂`.

The descent of constructibility from the middle term to the outer ones is the hypothesis
`hconstructible`; the source obtains it from Proposition 09BH. Everything else is proved.

Since the constructibility descent is carried, this is a reference to Stacks Project, Tag 0A5C and
not a registration of it; the per-statement registrations of the tag are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension`. -/
theorem curveCohomologyStatements_X₂_of_shortExact_of_constructible_and (hS : S.ShortExact)
    (hconstructible : constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (h₁ : CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₁)
    (h₃ : CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₃) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₂ where
  vanishing q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact.{u, v, w} hS h₁.vanishing h₃.vanishing q hq
  vanishing_of_isAffine hZ q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine.{u, v, w} hS
      h₁.vanishing_of_isAffine h₃.vanishing_of_isAffine hZ q hq
  vanishing_of_isPrimePowerTorsion h₂ q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion.{u, v, w} l hS
      h₁.vanishing_of_isPrimePowerTorsion h₃.vanishing_of_isPrimePowerTorsion h₂ q hq
  finite_of_isPrimeToCharacteristicTorsion hconstr h₂ q := by
    obtain ⟨hc₁, hc₃⟩ := hconstructible hconstr
    obtain ⟨ht₁, ht₃⟩ := isPrimeToCharacteristicTorsion_of_shortExact p hS h₂
    have := h₁.finite_of_isPrimeToCharacteristicTorsion hc₁ ht₁ q
    have := h₃.finite_of_isPrimeToCharacteristicTorsion hc₃ ht₃ q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  finite_of_isProper hconstr hπ q := by
    obtain ⟨hc₁, hc₃⟩ := hconstructible hconstr
    have := h₁.finite_of_isProper hc₁ hπ q
    have := h₃.finite_of_isProper hc₃ hπ q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  bijective_restriction_of_isPrimeToCharacteristicTorsion h₂ q :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion.{u,
        v, w} i p hS h₁.bijective_restriction_of_isPrimeToCharacteristicTorsion
      h₃.bijective_restriction_of_isPrimeToCharacteristicTorsion h₂ q
  bijective_restriction_of_isProper hπ q :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isProper.{u, v, w} i π hS
      h₁.bijective_restriction_of_isProper h₃.bijective_restriction_of_isProper hπ q
  surjective_restriction :=
    surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing.{u, v, w} i hS
      h₁.vanishing h₁.surjective_restriction h₃.surjective_restriction

end Stacks.EtaleCohomology

end
