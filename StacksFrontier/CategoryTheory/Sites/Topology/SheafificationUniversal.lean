module

public import Mathlib.CategoryTheory.Sites.Sheafification

import StacksCore.Tactic.StacksAttribute

/-!
# The universal property of sheafification

Stacks 00ZM is the universal property of sheafification: the canonical map `F ⟶ F^#` is initial
among maps from `F` into a sheaf, so every morphism `φ : F ⟶ G` with `G` a sheaf factors uniquely
through it.

That existence-and-uniqueness statement is Mathlib's sheafification adjunction. Its unit is the
canonical map `CategoryTheory.toSheafify`, and `CategoryTheory.sheafificationAdjunction` is the
natural bijection `Mor_{Sh(C)}(F^#, G) ≃ Mor_{PSh(C)}(F, G)` given by composing with it, which is
exactly the unique factorization.
-/

@[expose] public section

-- The former @[stacks 00ZM] declaration is now the Mathlib declarations.
add_to_stacks 00ZM "the canonical map `F ⟶ F^#` to the sheafification, the unit of the
  adjunction" CategoryTheory.toSheafify
add_to_stacks 00ZM "composing with the canonical map is a bijection
  `Mor_{Sh(C)}(F^#, G) ≃ Mor_{PSh(C)}(F, G)`, i.e. every map from `F` into a sheaf factors
  uniquely through `F ⟶ F^#`" CategoryTheory.sheafificationAdjunction
