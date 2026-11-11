module

public import Mathlib.Algebra.Field.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Division rings

A skew field in the sense of Stacks (a ring with `1 ≠ 0` in which every nonzero element is
invertible) is Mathlib's `DivisionRing`.
-/

add_to_stacks 0740 "a skew field is a `DivisionRing`" DivisionRing
