module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes

import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Separated presheaves for a topology

Stacks 00ZI calls a presheaf of sets `F` *separated* for a topology `J` when for every object `U`
and every covering sieve `S` on `U` the canonical map `F U ⟶ Mor_{PSh(C)}(S, F)` is injective.

That injectivity is Mathlib's `CategoryTheory.Presieve.IsSeparatedFor`, and quantifying it over
the covering sieves of `J` is exactly Mathlib's `CategoryTheory.Presieve.IsSeparated`.
-/

@[expose] public section

-- The former @[stacks 00ZI] declaration is now the Mathlib predicate.
add_to_stacks 00ZI "a presheaf of sets is separated for `J` when the canonical map
  `F U ⟶ Mor_{PSh(C)}(S, F)` is injective for every covering sieve `S` on every `U`"
  CategoryTheory.Presieve.IsSeparated
add_to_sga "3 IV 4.3.18" CategoryTheory.Presieve.IsSeparated
add_to_sga "3 XXII 4.1.11" CategoryTheory.Presieve.IsSeparated
add_to_sga "4 II 2.7" CategoryTheory.Presieve.IsSeparated
add_to_sga "4 II 3.2" CategoryTheory.Presieve.IsSeparated
add_to_sga "3 IV 4.3.1" "separated presheaf" CategoryTheory.Presieve.IsSeparated
add_to_sga "4 II 2.1" "separated clause"
  CategoryTheory.Presieve.IsSeparated
