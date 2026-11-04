module

public import Mathlib.Topology.Sheaves.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008F — Pullback ⊣ pushforward on presheaves

Stacks 008F says that for a continuous map `f : X → Y` there is a functor
`f_p : PSh(Y) → PSh(X)` left adjoint to `f_*`, determined by
`f_p G(U) = colim_{f(U) ⊆ V} G(V)`.

Mathlib has the two functors and the adjunction: `TopCat.Presheaf.pushforward` is `f_*`,
`TopCat.Presheaf.pullback` is `f_p` (constructed as the left Kan extension, i.e. by that
colimit), and `TopCat.Presheaf.pullbackPushforwardAdjunction` is the adjunction.
`TopCat.Presheaf.pullbackObjObjOfImageOpen` evaluates `f_p G` where the image of the open is
itself open, which is as far as Mathlib spells the colimit formula out.
-/

@[expose] public section

-- The former @[stacks 008F] definition was `pullbackPushforwardAdjunction`, and the two
-- functors it relates were abbreviations for Mathlib's.
add_to_stacks 008F "the pushforward `f_*` on presheaves" TopCat.Presheaf.pushforward
add_to_sga "4 IV 4.1.1" "(F)" TopCat.Presheaf.pushforward
add_to_ega "0 3.4.1" TopCat.Presheaf.pushforward
add_to_ega "0 3.4.2" TopCat.Presheaf.pushforward
add_to_stacks 008F "the pullback `f_p` on presheaves, the left Kan extension along `Opens.map f`"
  TopCat.Presheaf.pullback
add_to_stacks 008F "`f_p` is left adjoint to `f_*`"
  TopCat.Presheaf.pullbackPushforwardAdjunction
add_to_stacks 008F "the value of `f_p G` on an open with open image"
  TopCat.Presheaf.pullbackObjObjOfImageOpen
