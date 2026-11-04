module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006I — Products of presheaves of sets

Stacks 006I states that the category of presheaves of sets on a topological space `X` has
products, and that the set of sections of a product `F × G` over an open `U` is the product of
the sets of sections of `F` and of `G` over `U`.

Both halves are Mathlib's. Presheaves of sets on `X` form the functor category
`(Opens X)ᵒᵖ ⥤ Type u`, which has limits of every shape because `Type u` does, by
`CategoryTheory.Limits.functorCategoryHasLimitsOfShape`; products are the case of a discrete
shape. That a binary product is computed sectionwise is
`CategoryTheory.FunctorToTypes.binaryProductEquiv`, the bijection sending a section of `F ⨯ G`
over `U` to the pair of its two projections.
-/

@[expose] public section

-- The former @[stacks 006I] theorems were `inferInstance` and this Mathlib equivalence.
add_to_stacks 006I "presheaves of sets form a functor category, which has products because
  `Type u` does" CategoryTheory.Limits.functorCategoryHasLimitsOfShape
add_to_sga "4 I 9.6" "(ii)" CategoryTheory.Limits.functorCategoryHasLimitsOfShape
add_to_stacks 006I "sections of a binary product over `U` are pairs of sections over `U`"
  CategoryTheory.FunctorToTypes.binaryProductEquiv
