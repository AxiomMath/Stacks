module

public import Mathlib.Topology.Sheaves.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Presheaves of sets on a topological space

A presheaf of sets on `X` assigns a set `F(U)` to each open `U ⊆ X` and a restriction map
`ρ^U_V : F(U) → F(V)` to each inclusion `V ⊆ U`, subject to `ρ^U_U = id` and
`ρ^U_W = ρ^V_W ∘ ρ^U_V`; a morphism of presheaves is a family of maps `F(U) → G(U)` compatible
with the restriction maps, and presheaves of sets on `X` form the category `PSh(X)`.

In Mathlib a presheaf of `C`-objects on `X` is a contravariant functor `(Opens X)ᵒᵖ ⥤ C`,
namely `TopCat.Presheaf C X`. At `C = Type u` the action on objects is `U ↦ F(U)`, the action on
morphisms gives the restriction maps, and the functoriality laws `map_id` and `map_comp` are the
two axioms above. Morphisms of presheaves are natural transformations, naturality being
compatibility with the restriction maps, and the category is `TopCat.instCategoryPresheaf`.

## References

* [Stacks Project, Tag 006E](https://stacks.math.columbia.edu/tag/006E)
-/

@[expose] public section

add_to_stacks 006E "a presheaf of sets on `X` is a functor `(Opens X)ᵒᵖ ⥤ Type u`, whose
  `map_id` and `map_comp` are the axioms `ρ^U_U = id` and `ρ^U_W = ρ^V_W ∘ ρ^U_V`; the objects
  of `PSh(X)`" TopCat.Presheaf
add_to_stacks 006E "morphisms of presheaves of sets are natural transformations, naturality
  being compatibility with the restriction maps; the category `PSh(X)`"
  TopCat.instCategoryPresheaf
