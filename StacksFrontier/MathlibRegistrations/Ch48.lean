module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations for Stacks Chapter 48 (Duality for Schemes)

Tags of this chapter whose statements are already in Mathlib, registered on the Mathlib
declarations that state them. Where a tag is covered by several declarations, each registration
names the part it gives.
-/

@[expose] public section

add_to_stacks 0A9J "the cartesian square of a base change" CategoryTheory.IsPullback
