module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# A closed immersion is an isomorphism on residue fields

A closed immersion is surjective on stalks, and the residue field of a local ring is a quotient
of it, so the induced map of residue fields is surjective; it is injective because a map of
fields is. Hence it is an isomorphism.

## Main results

* `AlgebraicGeometry.residueFieldMap_isIso_of_isClosedImmersion`: the residue field map of a
  closed immersion at a point is an isomorphism.

## Implementation notes

The module imports only the two Mathlib files that carry `Scheme.Hom.residueFieldMap` and
`IsClosedImmersion`, so any module using the statement can import it at no extra cost.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The residue field map of a closed immersion is an isomorphism.** It is injective because
it is a map of fields, and surjective because a closed immersion is surjective on stalks and the
residue field is a quotient of the stalk. -/
public theorem residueFieldMap_isIso_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective (f.residueFieldMap x)).2 ⟨RingHom.injective _, by
    intro z
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, ha⟩ := f.stalkMap_surjective x b
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    show IsLocalRing.ResidueField.map (f.stalkMap x).hom
      (IsLocalRing.residue _ a) = _
    rw [IsLocalRing.ResidueField.map_residue, ha, hb]⟩

end AlgebraicGeometry

end
