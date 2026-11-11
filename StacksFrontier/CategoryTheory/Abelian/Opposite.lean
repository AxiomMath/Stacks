module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Additive categories and opposites

Stacks, Definition 0104, calls a category additive if it is preadditive and has finite products,
equivalently a zero object and direct sums. For a preadditive category `C`, this file shows that
`C` is additive if and only if `Cᵒᵖ` is, in both of these forms. The preadditivity of `Cᵒᵖ` and
the abelian clause of Stacks, Lemma 010A are registered in
`StacksCore/CategoryTheory/Abelian/Opposite.lean`.

## Main results

* `CategoryTheory.Preadditive.hasFiniteProducts_op_iff`: a preadditive category has finite
  products if and only if its opposite does.
* `CategoryTheory.Preadditive.hasZeroObject_and_hasFiniteBiproducts_op_iff`: a preadditive
  category has a zero object and finite biproducts if and only if its opposite does.

## References

* [Stacks, Tag 010A]
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- A preadditive category has finite products if and only if its opposite category does. With
Stacks' definition of an additive category (preadditive with finite products), this says `C` is
additive if and only if `Cᵒᵖ` is. -/
@[stacks 010A "the additive clause, for additive = preadditive with finite products \
  (Definition 0104)"]
theorem hasFiniteProducts_op_iff : HasFiniteProducts Cᵒᵖ ↔ HasFiniteProducts C := by
  constructor
  · intro _
    have : HasFiniteBiproducts Cᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
    exact hasFiniteProducts_of_opposite (C := C)
  · intro _
    have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
    infer_instance

/-- A preadditive category has a zero object and finite biproducts (direct sums) if and only if
its opposite category does: the additive clause of Stacks, Lemma 010A, with additivity
characterized by a zero object and direct sums as in its proof. -/
@[stacks 010A "the additive clause, for additive = preadditive with a zero object and \
  direct sums"]
theorem hasZeroObject_and_hasFiniteBiproducts_op_iff :
    (HasZeroObject Cᵒᵖ ∧ HasFiniteBiproducts Cᵒᵖ) ↔ (HasZeroObject C ∧ HasFiniteBiproducts C) := by
  constructor
  · rintro ⟨_, _⟩
    have : HasFiniteProducts C := hasFiniteProducts_op_iff.mp inferInstance
    exact ⟨hasZeroObject_unop (C := C), HasFiniteBiproducts.of_hasFiniteProducts⟩
  · rintro ⟨_, _⟩
    have : HasFiniteProducts Cᵒᵖ := hasFiniteProducts_op_iff.mpr inferInstance
    exact ⟨inferInstance, HasFiniteBiproducts.of_hasFiniteProducts⟩

end CategoryTheory.Preadditive
