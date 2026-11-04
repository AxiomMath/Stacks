module

public import Mathlib.CategoryTheory.Filtered.Final

import StacksCore.Tactic.StacksAttribute

/-!
# Full subcategories of a filtered category that absorb every object

Stacks 0BUC: if `ℐ` is filtered and `𝒥 ⊆ ℐ` is a full subcategory such that every object of
`ℐ` admits a morphism into an object of `𝒥`, then `𝒥` is filtered and cofinal in `ℐ`.

Both halves are Mathlib's, stated there for an arbitrary fully faithful functor rather than
for the inclusion of a full subcategory, and proved from the same reference
[Kashiwara–Schapira, Proposition 3.2.4].
-/

@[expose] public section

-- The former @[stacks 0BUC] lemmas are the Mathlib theorems, applied to a full
-- subcategory's inclusion `P.ι`, which is fully faithful.
add_to_stacks 0BUC "the subcategory is filtered"
  CategoryTheory.IsFiltered.of_exists_of_isFiltered_of_fullyFaithful
add_to_sga "4 I 8.1.3" "c)" CategoryTheory.IsFiltered.of_exists_of_isFiltered_of_fullyFaithful
add_to_stacks 0BUC "the inclusion is cofinal, i.e. final"
  CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful
add_to_sga "4 I 8.1.3" "c)" CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful
add_to_sga "4 I 8.1.4" "cofinal subset ⇒ final"
  CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful

end
