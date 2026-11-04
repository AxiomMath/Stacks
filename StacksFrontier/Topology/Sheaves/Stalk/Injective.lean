module

public import Mathlib.Topology.Sheaves.Stalks

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0079 — sections of a sheaf of sets are determined by their germs

For a sheaf of sets `F` on a topological space `X` and every open set `U`, the canonical map
`F(U) → ∏_{x ∈ U} F_x` to the product of stalks is injective; equivalently, two sections
`s, t : F(U)` are equal as soon as they have the same germ at every point of `U`.

Mathlib states this in the second, extensionality form, as `TopCat.Presheaf.section_ext`; the
injectivity of the map into the product of stalks is that statement read for the two sections
`s` and `t`.
-/

@[expose] public section

-- The former @[stacks 0079] theorem is this Mathlib theorem, stated as extensionality.
add_to_stacks 0079 "two sections with the same germ at every point of `U` are equal"
  TopCat.Presheaf.section_ext
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Presheaf.section_ext
