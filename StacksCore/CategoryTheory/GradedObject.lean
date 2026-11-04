module

public import Mathlib.CategoryTheory.GradedObject
public import StacksCore.CategoryTheory.Limits.Shapes.FiniteProducts
import StacksCore.Tactic.StacksAttribute

/-! # Graded objects

Stacks 0125 defines the category `Gr(𝒜)` of graded objects of an additive category `𝒜`:
objects are `ℤ`-indexed families of objects of `𝒜` and morphisms are families of morphisms.
Mathlib's `CategoryTheory.GradedObject β C` is this for an arbitrary index type `β` and an
arbitrary category `C`, with the pointwise category structure: a morphism *is* a family
`∀ i, X i ⟶ Y i`.

Stacks 09MG defines the `k`-th shift of a graded object by `A[k]^i = A^{k + i}`. Mathlib has
this as `CategoryTheory.GradedObject.hasShift`, generalized to translation by any element `s`
of an `AddCommGroup` grading: shifting by `n : ℤ` reindexes along `b ↦ b + n • s`, so at
`β := ℤ`, `s := 1` the computation rule `shiftFunctor_obj_apply` reads `(A⟦k⟧)^i = A^{i + k}`,
the tag's definition up to `add_comm`. The instance lives on the type synonym
`GradedObjectWithShift s C` rather than on `GradedObject ℤ C` itself, because `s` does not
occur in the underlying type, so instance search could never recover it from the bare type.

`hasMap_of_finite` is the graded-object reading of the existence remark after Stacks 012Z: the
coproducts `X.mapObj p` needs exist when finite coproducts do and each fibre of `p` carries only
finitely many nonzero terms.
-/

@[expose] public section

add_to_stacks 0125 "for an arbitrary index type and an arbitrary category"
  CategoryTheory.GradedObject
add_to_stacks 0125 "the category structure" CategoryTheory.GradedObject.categoryOfGradedObjects

add_to_stacks 09MG "for translation by any `s` in an `AddCommGroup` grading; the tag is `s := 1`"
  CategoryTheory.GradedObject.hasShift
add_to_stacks 09MG "the computation rule: at `s := 1` it is the tag's `A[k]^i = A^{k + i}`"
  CategoryTheory.GradedObject.shiftFunctor_obj_apply
add_to_stacks 09MG "the shift on morphisms" CategoryTheory.GradedObject.shiftFunctor_map_apply

namespace CategoryTheory.GradedObject

variable {C : Type*} [Category* C]

/-- A graded object with finitely many nonzero terms over each fibre of `p` has the coproducts
that `X.mapObj p` needs, as soon as finite coproducts exist. -/
theorem hasMap_of_finite {I J : Type*} [Limits.HasFiniteCoproducts C] (X : GradedObject I C)
    (p : I → J) (h : ∀ j, {i | p i = j ∧ ¬ Limits.IsZero (X i)}.Finite) : X.HasMap p := fun j =>
  Limits.hasCoproduct_of_finite_not_isZero _
    (((h j).preimage Subtype.val_injective.injOn).subset fun i hi => ⟨i.2, hi⟩)

end CategoryTheory.GradedObject
