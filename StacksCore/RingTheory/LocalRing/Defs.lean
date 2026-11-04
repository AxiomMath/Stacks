module

public import Mathlib.RingTheory.LocalRing.Defs
import StacksCore.Tactic.StacksAttribute

/-! # Local rings

Stacks tag 07BI, first sentence: a local ring is a ring with exactly one maximal ideal.

Mathlib's `IsLocalRing` is *defined* differently — it asks that the ring be nontrivial and that
`a` or `b` be a unit whenever `a + b = 1`. The two agree, and the bridge in the Stacks
project's own wording is `IsLocalRing.maximal_ideal_unique`, tagged in
`StacksCore.RingTheory.LocalRing.MaximalIdeal.Basic`. Both carry the tag: the definition because
that is what a reader following 07BI should land on, the bridge because it is what licenses
calling them the same notion. The equivalence is also clause (1) ⇔ (3) of tag 00E9.
-/

@[expose] public section

add_to_stacks 07BI "A local ring is a ring with exactly one maximal ideal. Mathlib defines this
  by the equivalent condition that the ring is nontrivial and `a` or `b` is a unit whenever
  `a + b = 1`; see `IsLocalRing.maximal_ideal_unique` for the Stacks wording." IsLocalRing
