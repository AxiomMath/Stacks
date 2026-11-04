module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterization of universal homeomorphisms

A morphism of schemes is a universal homeomorphism exactly when it is integral, universally
injective, and surjective.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_iff_integral_universallyInjective_surjective`
  characterizes universal homeomorphisms by three standard properties of morphisms.

## Implementation notes

The three conditions in the characterization use Mathlib's predicate classes `IsIntegralHom`,
`UniversallyInjective`, and `Surjective`.

## References

* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is a universal homeomorphism if and only if it is integral,
universally injective, and surjective. -/
@[stacks 04DF,
  ega "IV 18.12.11" "integral case",
  ega "IV 2.4.5" "(i)",
  ega "IV 15.2.4" "more general", sga "4 VIII 1.4"]
theorem universalHomeomorphism_iff_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      IsIntegralHom f ∧ UniversallyInjective f ∧ Surjective f := by
  constructor
  · intro hf
    have hhomeo : IsHomeomorph f := hf.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
    refine ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
        ⟨⟨fun _ _ _ _ _ H => (hf.universally_isHomeomorph _ _ _ H).isClosedMap⟩,
          isAffineHom_of_isInducing f hhomeo.isEmbedding.isInducing
            (by rw [Set.range_eq_univ.mpr hhomeo.bijective.2]; exact isClosed_univ)⟩,
      ⟨fun _ _ _ _ _ H => (hf.universally_isHomeomorph _ _ _ H).injective⟩,
      ⟨hhomeo.bijective.2⟩⟩
  · rintro ⟨hint, hinj, hsurj⟩
    have : UniversallyClosed f := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hint).1
    refine ⟨fun _ _ _ _ f' H => ?_⟩
    have : Surjective f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip hsurj
    exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨Scheme.Hom.continuous _, UniversallyClosed.universally_isClosedMap _ _ _ H,
        ⟨UniversallyInjective.universally_injective _ _ _ H, f'.surjective⟩⟩

end AlgebraicGeometry

end
