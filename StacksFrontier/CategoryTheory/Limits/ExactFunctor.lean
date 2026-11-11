module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Left exact, right exact and exact functors

This file registers Stacks, Definition 0034 on Mathlib's notions of left exact, right exact and
exact functors, all three parts of the definition.

Mathlib states each notion without assuming that the finite limits (resp. finite colimits) exist
in the source: a functor preserves finite limits when it sends every limit cone over a finite
diagram to a limit cone. When all finite limits (resp. colimits) exist in the source, as Stacks
assumes, this is exactly "commutes with all finite limits (resp. finite colimits)".
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 0034 "Part (1), left exact functors: the property `leftExactFunctor C D` of a functor
  `F : C ⥤ D`, which is `PreservesFiniteLimits F` (`leftExactFunctor_iff`); left exact functors
  form the full subcategory `C ⥤ₗ D`." leftExactFunctor

add_to_stacks 0034 "Part (2), right exact functors: the property `rightExactFunctor C D` of a
  functor `F : C ⥤ D`, which is `PreservesFiniteColimits F` (`rightExactFunctor_iff`); right
  exact functors form the full subcategory `C ⥤ᵣ D`." rightExactFunctor

add_to_stacks 0034 "Part (3), exact functors: the property `exactFunctor C D` of a functor
  `F : C ⥤ D`, which is `PreservesFiniteLimits F ∧ PreservesFiniteColimits F`, i.e. both left and
  right exact (`exactFunctor_iff`, `exactFunctor_le_leftExactFunctor`,
  `exactFunctor_le_rightExactFunctor`); exact functors form the full subcategory `C ⥤ₑ D`."
  exactFunctor

add_to_stacks 0034 "Part (3): a functor is exact iff it preserves finite limits and finite
  colimits." exactFunctor_iff
