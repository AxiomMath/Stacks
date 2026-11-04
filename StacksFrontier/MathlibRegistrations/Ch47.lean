module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations: Dualizing complexes (Stacks Chapter 47)

Stacks tags from the chapter *Dualizing complexes* whose statements Mathlib already proves,
recorded on the Mathlib declarations with `add_to_stacks`.

## References

* [Stacks Project, Chapter 47](https://stacks.math.columbia.edu/tag/08XG)
-/

-- Any product of injective `R`-modules is injective.
add_to_stacks 08XP Module.Injective.pi

-- Definition: an indecomposable object of an additive category.
add_to_stacks 08Y6
  "for any category with zero morphisms and binary biproducts, e.g. an additive category"
  CategoryTheory.Indecomposable
