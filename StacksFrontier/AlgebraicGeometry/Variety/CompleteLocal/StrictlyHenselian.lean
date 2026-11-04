module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import StacksCore.Tactic.StacksAttribute

/-!
# Strictly henselian local rings

A local ring is strictly henselian when it is henselian and its residue field is separably
closed.

## Main definitions

* `StrictlyHenselianLocalRing` is the property of being a henselian local ring with separably
  closed residue field.

## Implementation notes

The property is a class extending both `HenselianLocalRing R` and
`IsSepClosed (IsLocalRing.ResidueField R)`. Consequently, either constituent property is
available directly by typeclass inference from strict henselianity.

## References

* [Stacks Project, Tag 03QK](https://stacks.math.columbia.edu/tag/03QK)
-/

@[expose] public section

/-- A commutative ring is strictly henselian if it is a henselian local ring and its
residue field is separably closed. -/
@[stacks 03QK,
  sga "7 XIII 0.2" "(0.2.3) ring case", sga "4 VIII 4.2" "(i)", sga "7 I 0.0.2" "ring case"]
class StrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop extends
  HenselianLocalRing R, IsSepClosed (IsLocalRing.ResidueField R)
