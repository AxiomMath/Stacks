module

public import Mathlib.Topology.Sheaves.Skyscraper

import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 009B — stalks of a skyscraper sheaf

Let `X` be a topological space, `x` a point of `X` and `A` a set. Tag 009B computes the stalks
of the skyscraper sheaf `i_{x,*}A`, whose sections over `U` are `A` if `x ∈ U` and a single
point otherwise: the stalk at `x'` is `A` when `x'` lies in the closure of `{x}` — equivalently
when `x` specializes to `x'` — and a singleton otherwise.

Mathlib has the skyscraper sheaf (`skyscraperSheaf`, over any target category with a terminal
object, the decidability of `x ∈ U` taken classically) and both cases of the stalk computation,
phrased with specialization rather than closure: `skyscraperPresheafStalkOfSpecializes` and
`skyscraperPresheafStalkOfNotSpecializes`. The two phrasings agree by Mathlib's
`specializes_iff_mem_closure`, and for sets the terminal object is `PUnit` by
`CategoryTheory.Limits.Types.terminalIso`.
-/

@[expose] public section

-- The former @[stacks 009B] definitions instantiated Mathlib's skyscraper sheaf at `Type u` and
-- restated these two Mathlib isomorphisms using closure instead of specialization.
add_to_stacks 009B "the skyscraper sheaf `i_{x,*}A`" skyscraperSheaf
add_to_stacks 009B "stalk at a point of the closure of `{x}`, i.e. a specialization of `x`: it
  is `A`" skyscraperPresheafStalkOfSpecializes
add_to_ega "IV 21.9.1" "stalk on closure"
  skyscraperPresheafStalkOfSpecializes
add_to_stacks 009B "stalk at a point outside the closure of `{x}`: it is terminal, a singleton
  for sheaves of sets" skyscraperPresheafStalkOfNotSpecializes
add_to_ega "IV 21.9.1" "stalk off closure"
  skyscraperPresheafStalkOfNotSpecializes
