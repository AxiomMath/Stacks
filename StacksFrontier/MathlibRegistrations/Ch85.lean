module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of Chapter 85 (Simplicial Spaces) covered by Mathlib

Tags of the chapter on simplicial spaces whose content Mathlib states, recorded on the Mathlib
declarations.

## References

* [Stacks Project, Tag 0249](https://stacks.math.columbia.edu/tag/0249)
-/

@[expose] public section

add_to_stacks 0249 "more general: an equifibered natural transformation of functors J ⥤ C; here \
  J = SimplexCategoryᵒᵖ and C = Scheme, so a morphism of simplicial schemes"
  CategoryTheory.NatTrans.Equifibered

end
