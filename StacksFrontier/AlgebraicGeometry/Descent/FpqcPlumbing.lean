module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shared re-packagings for fpqc descent of properties of morphisms

The fpqc descent of a property of morphisms of schemes is proved, in this development, from the
criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (the fpqc case of Tag 02KP) together
with a descent step along the morphism property `Surjective ⊓ Flat ⊓ QuasiCompact`.  Setting that
up needs a handful of facts which Mathlib has but does not expose as instances: instance
synthesis cannot solve for the ring-homomorphism parameter of
`AlgebraicGeometry.HasRingHomProperty`, nor match a morphism property appearing as a factor of an
infimum, and the stability of an infimum of morphism properties under base change and under
composition is a lemma rather than an instance.

This file collects those facts so that each fpqc descent proof can use them instead of restating
them.  Nothing here is mathematics: every declaration is a re-packaging of a Mathlib instance or
lemma.

## Main results

* `Stacks.Descent.flat_isZariskiLocalAtSource`: flatness is Zariski local at the source.
* `Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat` and
  `Stacks.Descent.isStableUnderComposition_surjective_inf_flat`: surjective flat morphisms are
  stable under base change and under composition.
* `Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact`: surjective flat
  quasi-compact morphisms are stable under base change.
* `Stacks.Descent.isLocalIso_inf_surjective_le_surjective_inf_flat`: a surjective local
  isomorphism is surjective and flat.  This is the hypothesis of
  `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`, which reduces a
  descent step to the case of a surjective flat morphism of affine schemes.

## Implementation notes

These five statements were previously `private` lemmas repeated verbatim in
`StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget`,
`StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine` and — for the last base-change
stability — `StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget`.  They are public
here so that the next fpqc descent proof does not restate them a fourth time.

No Stacks tag is claimed: the contents carry no mathematical content of their own.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- Flat morphisms are Zariski local at the source. -/
@[sga "4 IV 8.5.5" "special case"]
lemma flat_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)

/-- Surjective flat morphisms are stable under base change. -/
lemma isStableUnderBaseChange_surjective_inf_flat :
    MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u}) (@Surjective ⊓ @Flat) := .inf

/-- Surjective flat morphisms are stable under composition. -/
lemma isStableUnderComposition_surjective_inf_flat :
    MorphismProperty.IsStableUnderComposition (C := Scheme.{u}) (@Surjective ⊓ @Flat) :=
  have := instIsMultiplicativeSchemeSurjective.{u}.toIsStableUnderComposition
  .inf

/-- Surjective flat quasi-compact morphisms are stable under base change. -/
@[ega "I 6.6.4" "(iii), special case"]
lemma isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  have := isStableUnderBaseChange_surjective_inf_flat.{u}
  .inf

/-- A surjective local isomorphism is surjective and flat. -/
lemma isLocalIso_inf_surjective_le_surjective_inf_flat :
    (@IsLocalIso ⊓ @Surjective : MorphismProperty Scheme.{u}) ≤
      (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) := by
  have := flat_isZariskiLocalAtSource.{u}
  have := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
  intro X Y f hf
  exact ⟨hf.2, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hf.1⟩

end Stacks.Descent

end
