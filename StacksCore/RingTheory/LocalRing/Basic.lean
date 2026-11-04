module

public import Mathlib.RingTheory.LocalRing.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Local rings via the `x` or `1 - x` criterion

Stacks tag 00E9, clause (1) ⇔ (4): a ring is local if and only if it is not the zero ring and,
for every `x`, at least one of `x` and `1 - x` is invertible.

Both directions are already in Mathlib, and this is the clause where Mathlib and the Stacks
project agree on the *definition* rather than merely on the characterisation — `IsLocalRing` is
declared by exactly this condition (in the `a + b = 1` form), so (1) ⇒ (4) is essentially the
class field and (4) ⇒ (1) its constructor. The tag's "or both" is the inclusive `∨`, and "not
the zero ring" is `Nontrivial`.

The other two clauses need work on our side: (1) ⇔ (3) is in
`StacksCore.RingTheory.LocalRing.MaximalIdeal.Basic` and (1) ⇔ (2), the topological one, is in
`StacksCore.RingTheory.Spectrum.Prime.Topology`.
-/

@[expose] public section

add_to_stacks 00E9 "(1) ⇒ (4): in a local ring, `x` or `1 - x` is a unit."
  IsLocalRing.isUnit_or_isUnit_one_sub_self
add_to_stacks 00E9 "(4) ⇒ (1): a nontrivial ring in which `x` or `1 - x` is always a unit is
  local." IsLocalRing.of_isUnit_or_isUnit_one_sub_self
