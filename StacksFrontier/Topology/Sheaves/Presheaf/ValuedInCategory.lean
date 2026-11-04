module

public import Mathlib.Topology.Sheaves.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006N — Presheaves with values in a category

Stacks 006N defines (1) a presheaf `F` on a topological space `X` with values in a category
`C` as an object `F(U)` of `C` for every open `U ⊆ X` together with restriction morphisms
`ρ^U_V : F(U) → F(V)` composing as the inclusions do, and (2) a morphism of such presheaves
as a family `F(U) → G(U)` compatible with the restriction morphisms.

Both are Mathlib's `TopCat.Presheaf`, which is the functor category `(Opens X)ᵒᵖ ⥤ C`, with
morphisms the natural transformations (`TopCat.instCategoryPresheaf`). Since `TopCat.Presheaf`
takes the value category as a parameter, the same pair of declarations covers 006E, the
presheaf-of-sets case, as the instance `C = Type`.

One wrinkle, recorded because it is easy to trip over: 006N's printed composition law
`ρ^U_W = ρ^V_W ∘ ρ^U_V` does not by itself force `ρ^U_U = id` — taking `W = V = U` makes
`ρ^U_U` idempotent, no more — whereas a functor supplies it through `map_id`. Mathlib is
therefore strictly stronger than 006N's literal text by exactly that clause. It is read here
as an elision in the source rather than a distinct notion, because 006E states the very same
definition for sets one tag earlier and does spell `ρ^U_U = id` out, and because nothing
downstream uses a presheaf whose restriction-to-self is merely idempotent.
-/

@[expose] public section

-- The former @[stacks_fixed 006N] structures, and the equivalences comparing them with
-- Mathlib's functorial encoding, are the Mathlib definitions themselves.
add_to_stacks 006N "(1), presheaves valued in a category" TopCat.Presheaf
add_to_stacks 006N "(2), their morphisms" TopCat.instCategoryPresheaf

end
