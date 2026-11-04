module

public import Mathlib.Topology.Sheaves.Stalks

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008G — the stalk of the pullback presheaf

For a continuous map `f : X ⟶ Y` and a presheaf of sets `G` on `Y`, the stalk of the pullback
presheaf `f_p G` at `x` is canonically in bijection with the stalk of `G` at `f x`.

Mathlib states this for presheaves valued in any category with colimits: the canonical map is
`TopCat.Presheaf.stalkPullbackHom` and the assertion that it is an isomorphism — for sets, a
bijection — is `TopCat.Presheaf.stalkPullbackIso`.
-/

@[expose] public section

-- The former @[stacks 008G] theorem is the bijectivity of this Mathlib isomorphism.
add_to_stacks 008G "the canonical map `G_{f x} ⟶ (f_p G)_x` of stalks"
  TopCat.Presheaf.stalkPullbackHom
add_to_stacks 008G "that map is an isomorphism, i.e. a bijection of stalks for sets"
  TopCat.Presheaf.stalkPullbackIso
