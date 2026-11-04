module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations: The trace formula (Stacks Chapter 64)

Stacks tags from the chapter *The trace formula* whose statements Mathlib already proves,
recorded on the Mathlib declarations with `add_to_stacks`.

## References

* [Stacks Project, Chapter 64](https://stacks.math.columbia.edu/tag/0F5P)
-/

-- An object `E` of `D(A)` lies in `D^+(A)` iff `H^i(E) = 0` for `i ≪ 0`; similarly `D^-`, `D^b`.
add_to_stacks 03T5 "D^+, with `TStructure.plus`" DerivedCategory.isGE_iff
add_to_stacks 03T5 "D^+: `t.plus X` is `∃ n, t.IsGE X n`"
  CategoryTheory.Triangulated.TStructure.plus
add_to_stacks 03T5 "D^-, with `TStructure.minus`" DerivedCategory.isLE_iff
add_to_stacks 03T5 "D^-: `t.minus X` is `∃ n, t.IsLE X n`"
  CategoryTheory.Triangulated.TStructure.minus
add_to_stacks 03T5 "D^b: `t.bounded` is `t.plus ⊓ t.minus`"
  CategoryTheory.Triangulated.TStructure.bounded
