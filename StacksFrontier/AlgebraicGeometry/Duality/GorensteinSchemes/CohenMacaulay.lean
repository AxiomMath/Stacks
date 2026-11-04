module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay

/-!
# Gorenstein schemes are Cohen–Macaulay

A Gorenstein scheme is Cohen–Macaulay: it is locally Noetherian, and each of its local rings,
being a Gorenstein local ring, is a Cohen–Macaulay local ring.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_of_isGorenstein`: a Gorenstein scheme is Cohen–Macaulay.

## Implementation notes

The Cohen–Macaulay property of a scheme is defined by affine opens, so it is reached through its
characterization by the local rings at the points; the local statement is then the
commutative-algebra fact that a Gorenstein local ring is Cohen–Macaulay.

## References

* [Stacks Project, Tag 0C00](https://stacks.math.columbia.edu/tag/0C00)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0C00.** Every Gorenstein scheme is Cohen–Macaulay. -/
@[stacks 0C00]
public theorem isCohenMacaulay_of_isGorenstein (X : Scheme.{u}) [IsGorenstein X] :
    IsCohenMacaulay X :=
  ((isCohenMacaulay_tfae_stalk X).out 2 1 rfl rfl).mp
    ⟨inferInstance, fun x => ⟨inferInstance,
      Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing (X.presheaf.stalk x)
        (IsGorenstein.isGorensteinLocalRing x)⟩⟩

end AlgebraicGeometry

end
