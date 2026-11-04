module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006T — Sheaves of sets on a topological space

Stacks 006T defines (1) a sheaf of sets on `X` as a presheaf of sets in which, for every open
covering `U = ⋃ i, U i`, a family of sections `s i ∈ F(U i)` agreeing on the pairwise
intersections glues to a unique section over `U`; (2) a morphism of sheaves of sets as a
morphism of the underlying presheaves of sets; and (3) the category `Sh(X)`.

Mathlib states all three. Clause (1) is `TopCat.Presheaf.IsSheafUniqueGluing`, the
unique-gluing condition written out, together with
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types`, its equivalence with Mathlib's
categorical sheaf condition, and `TopCat.Sheaf.existsUnique_gluing`, the unique gluing itself.
Clause (2) is `TopCat.Sheaf.forget`, the fully faithful forgetful functor to presheaves. Clause
(3) is `TopCat.Sheaf` with `TopCat.instCategorySheaf`; Mathlib has no notation `Sh(X)`.
-/

@[expose] public section

-- The former @[stacks 006T] declarations were these Mathlib notions restated, clause (1) in a
-- form whose covering index type may live in a larger universe than the space; that extra
-- generality is a `ULift` of Mathlib's statement and is not part of the tag.
add_to_stacks 006T "the unique-gluing sheaf condition for a presheaf of sets"
  TopCat.Presheaf.IsSheafUniqueGluing
add_to_sga "4½ Arcata 1.2.3" TopCat.Presheaf.IsSheafUniqueGluing
add_to_sga "4½ Arcata 1.6.3" "topological site" TopCat.Presheaf.IsSheafUniqueGluing
add_to_sga "4 II 2.1" "opens of a space" TopCat.Presheaf.IsSheafUniqueGluing
add_to_ega "0 3.1.2" "concrete category C" TopCat.Presheaf.IsSheafUniqueGluing
add_to_stacks 006T "agreement of the unique-gluing condition with the categorical one"
  TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
add_to_sga "4½ Arcata 1.6.3" "topological site"
  TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
add_to_ega "0 3.1.2" "C = Set" TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
add_to_stacks 006T "a compatible family over an open covering glues to a unique section"
  TopCat.Sheaf.existsUnique_gluing
add_to_sga "4½ Arcata 1.6.3" "topological site" TopCat.Sheaf.existsUnique_gluing
add_to_ega "0 3.1.2" "concrete category C" TopCat.Sheaf.existsUnique_gluing
add_to_stacks 006T "a morphism of sheaves of sets is a morphism of the underlying presheaves:
  the forgetful functor to presheaves is fully faithful" TopCat.Sheaf.forget
add_to_sga "3 IV 4.3.13" "special case" TopCat.Sheaf.forget
add_to_stacks 006T "sheaves of sets on `X`, the objects of `Sh(X)`" TopCat.Sheaf
add_to_sga "4½ Arcata 1.6.3" "topological site" TopCat.Sheaf
add_to_sga "4 II 2.1" "opens of a space" TopCat.Sheaf
add_to_ega "0 3.1.2" TopCat.Sheaf
add_to_stacks 006T "the category `Sh(X)`" TopCat.instCategorySheaf
add_to_sga "4 II 2.1" "opens of a space" TopCat.instCategorySheaf
