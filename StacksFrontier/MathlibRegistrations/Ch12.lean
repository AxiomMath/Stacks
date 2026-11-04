module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags covered by Mathlib: Chapter 12 (Homological algebra)

The Stacks tags below are stated in Mathlib. This file registers the Mathlib declarations that
realize them with `add_to_stacks`; it contains no declarations of its own.
-/

add_to_stacks 0105 "An additive functor transforms direct sums to direct sums (it preserves all
  finite biproducts)." CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive
add_to_stacks 0105 "Preserving biproducts indexed by a two-element type is preserving binary direct
  sums." CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts
add_to_stacks 0105 "An additive functor preserves zero morphisms."
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
add_to_stacks 0105 "A functor preserving zero morphisms transforms zero objects to zero objects."
  CategoryTheory.Functor.map_isZero
