module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.Gorenstein

/-!
# Gorenstein schemes

A scheme is Gorenstein when it is locally Noetherian and every stalk of its structure sheaf is
a Gorenstein local ring.

## Main definitions

* `AlgebraicGeometry.IsGorenstein` is the Gorenstein property for schemes.

## Main results

* `AlgebraicGeometry.isGorenstein_iff` characterizes Gorenstein schemes by local
  Noetherianity and pointwise Gorensteinness of their local rings.

## Implementation notes

The property is a typeclass, in keeping with scheme properties in Mathlib. Its inherited
`IsLocallyNoetherian` instance supplies the Noetherian structures on the stalks needed by
`Dualizing.IsGorensteinLocalRing`. The characterizing existential is the dependent form of the
conjunction in the source.

## References

* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme is Gorenstein if it is locally Noetherian and all of its local rings are
Gorenstein. -/
@[stacks 0AWW]
public class IsGorenstein (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  /-- The local ring at every point is Gorenstein. -/
  isGorensteinLocalRing (x : X) :
    letI : IsLocallyNoetherian X := toIsLocallyNoetherian
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)

/-- A scheme is Gorenstein exactly when it admits a locally Noetherian structure for which
all its local rings are Gorenstein. -/
@[simp]
public theorem isGorenstein_iff (X : Scheme.{u}) :
    IsGorenstein X ↔
      ∃ h : IsLocallyNoetherian X,
        letI : IsLocallyNoetherian X := h
        ∀ x : X, Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) :=
  ⟨fun h => ⟨h.toIsLocallyNoetherian, h.isGorensteinLocalRing⟩,
    fun ⟨hN, hG⟩ => { toIsLocallyNoetherian := hN, isGorensteinLocalRing := hG }⟩

end AlgebraicGeometry
