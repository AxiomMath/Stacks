module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Immersions into locally Noetherian schemes are quasi-compact

An immersion — a locally closed immersion — into a locally Noetherian scheme is quasi-compact.
The underlying reason is that a locally Noetherian scheme has a Noetherian, hence quasi-compact,
underlying space, and that this is inherited by open subschemes.

## Main results

* `AlgebraicGeometry.quasiCompact_of_isImmersion`: every immersion into a locally Noetherian
  scheme is quasi-compact.

## Implementation notes

The open-immersion case is
`AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion`. The general case is
reduced to it by the factorization of an immersion into a closed immersion followed by an open
immersion; a closed immersion is quasi-compact because a closed embedding pulls compact sets back
to compact sets.

The instance is given a low priority so that instance search tries the cheaper, more specific
open- and closed-immersion instances first.

## References

* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An immersion into a locally Noetherian scheme is quasi-compact. -/
@[stacks 01OX "all immersions", sga "3 VIB 1.4.2"]
instance (priority := 50) quasiCompact_of_isImmersion
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsImmersion f] : QuasiCompact f := by
  obtain ⟨W, a, b, ha, hb, hab⟩ := IsImmersion.isImmersion_iff_exists.mp ‹IsImmersion f›
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion b
  have : QuasiCompact a := ⟨fun _ _ hc => ha.isClosedEmbedding.isCompact_preimage hc⟩
  rw [← hab]
  infer_instance

end AlgebraicGeometry
