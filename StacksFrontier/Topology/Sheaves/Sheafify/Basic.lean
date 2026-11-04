module

public import Mathlib.Topology.Sheaves.Sheafify

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 007Y — the sheafification of a presheaf of sets is a sheaf

For a presheaf `F` of sets on a topological space `X`, the sheafification `F^#` constructed in
Stacks tag 007X is itself a sheaf.

In Mathlib the sheafification of a `Type`-valued presheaf on a topological space is
`TopCat.Presheaf.sheafify`, which is valued in `TopCat.Sheaf`: the sheaf property of `F^#` is
the second component of that bundled sheaf, so the statement of this tag is the type of
`TopCat.Presheaf.sheafify` itself.
-/

@[expose] public section

-- The former @[stacks 007Y] theorem is the sheaf condition bundled into this Mathlib definition.
add_to_stacks 007Y "the sheafification `F^#` of a presheaf of sets, as a sheaf"
  TopCat.Presheaf.sheafify
add_to_ega "0 3.7.1" TopCat.Presheaf.sheafify
