module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksCore.Tactic.StacksAttribute

/-!
# Resolutions of singularities

A resolution of singularities of a Noetherian integral scheme is a modification whose source
is regular.

## Main definitions

* `AlgebraicGeometry.IsResolution` is the predicate that a morphism is a resolution of
  singularities.

## Main results

* `AlgebraicGeometry.isResolution_iff` characterizes resolutions by the two defining
  properties.

## Implementation notes

The Noetherian and integral hypotheses on the target are retained as typeclass assumptions,
matching the context of the source definition. The predicate is an abbreviation, so clients
can directly use the APIs for modifications and regular schemes.

## References

* [Stacks Project, Tag 0BGK](https://stacks.math.columbia.edu/tag/0BGK)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism to a Noetherian integral scheme is a **resolution of singularities** if it is a
modification and its source is regular. -/
@[stacks 0BGK] abbrev IsResolution {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Y) : Prop := IsModification f ∧ IsRegular X

/-- The defining characterization of a resolution of singularities. -/
theorem isResolution_iff {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] (f : X ⟶ Y) :
    IsResolution f ↔ IsModification f ∧ IsRegular X := Iff.rfl

namespace IsResolution

/-- A resolution of singularities is a modification. -/
theorem isModification {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] {f : X ⟶ Y}
    (hf : IsResolution f) : IsModification f := hf.1

/-- The source of a resolution of singularities is regular. -/
theorem source_isRegular {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] {f : X ⟶ Y}
    (hf : IsResolution f) : IsRegular X := hf.2

end IsResolution

/-- A modification with regular source is a resolution of singularities. -/
theorem isResolution_of {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] (f : X ⟶ Y)
    (hmod : IsModification f) (hreg : IsRegular X) : IsResolution f := ⟨hmod, hreg⟩

end AlgebraicGeometry
