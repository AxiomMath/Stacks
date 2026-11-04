module

public import Mathlib.CategoryTheory.GradedObject.Braiding
import StacksCore.Tactic.StacksAttribute

/-! # The monoidal structure on graded objects

Stacks 0FFX is an example fixing conventions for graded `F`-vector spaces: the degreewise tensor
product `(V ⊗ W)ⁿ = ⨁_{n = p + q} Vᵖ ⊗_F W^q`, the associativity constraint, the unit `𝟏` (which
is `F` in degree `0` and zero elsewhere), and *two* commutativity constraints — "one involves the
intervention of signs and the other does not. We will usually use the one that does."

Mathlib supplies the monoidal structure and the sign-free symmetry at the level of
`GradedObject I C`, for a general grading and a general monoidal category, so the tag is attributed
there rather than to a graded-vector-space specialization. Neither instance is unconditional: both
need the coproducts the degreewise tensor product is built from, and need tensoring to preserve
them on either side, which is what the hypotheses named below amount to.

The signed (Koszul) constraint the tag says it will usually use is **not** in Mathlib for graded
objects: `GradedObject.Monoidal.braiding` is built from `C`'s own braiding and carries no sign. The
nearest signed map is `TensorProduct.gradedComm`, a `LinearEquiv` on internally graded modules
rather than a braiding here. That clause of 0FFX is therefore still open.

For the tag's own setting — the degreewise formula over a field — see
`StacksCore.CategoryTheory.GradedObject.GradedVectorSpace`.
-/

@[expose] public section

add_to_stacks 0FFX "the monoidal structure — tensor, unit, associator and unitors — for any
  `AddMonoid` grading with decidable equality and any monoidal category with an initial object and
  the coproducts the degreewise tensor product needs, preserved by tensoring on either side"
  CategoryTheory.GradedObject.monoidalCategory

add_to_stacks 0FFX "the sign-free commutativity constraint, which of the tag's two is the one it
  says it will *not* usually use; needs an `AddCommMonoid` grading and a symmetric `C`. The signed
  constraint the tag prefers is not in Mathlib for graded objects"
  CategoryTheory.GradedObject.symmetricCategory
