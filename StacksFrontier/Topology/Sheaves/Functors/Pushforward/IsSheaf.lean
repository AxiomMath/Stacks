module

public import Mathlib.Topology.Sheaves.Functors

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008D — the pushforward of a sheaf along a continuous map is a sheaf

For a continuous map `f : X ⟶ Y` of topological spaces and a sheaf `F` on `X`, the pushforward
presheaf `f _* F` on `Y` is again a sheaf: an open covering `V = ⋃ V_j` in `Y` pulls back to the
open covering `f ⁻¹ V = ⋃ f ⁻¹ V_j` in `X`, so the sheaf condition for `f _* F` on the cover
`{V_j}` is exactly the sheaf condition for `F` on `{f ⁻¹ V_j}`.

Mathlib states this as `TopCat.Sheaf.pushforward_sheaf_of_sheaf`, for presheaves valued in an
arbitrary category; the case of sheaves of sets is the target category `Type`.
-/

@[expose] public section

-- The former @[stacks 008D] theorem is this Mathlib theorem.
add_to_stacks 008D "the pushforward of a sheaf along a continuous map is a sheaf"
  TopCat.Sheaf.pushforward_sheaf_of_sheaf
add_to_ega "0 3.4.1" TopCat.Sheaf.pushforward_sheaf_of_sheaf
