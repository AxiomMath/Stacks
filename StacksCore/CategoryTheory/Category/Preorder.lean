module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Antisymmetrization

/-! # Preorders as categories
This file contains declarations that would belong in the mathlib file
`CategoryTheory/Category/Preorder.lean`.
-/

public section

namespace CategoryTheory

@[stacks 0CN1 "Every preorder is equivalent to its partial order quotient. In particular, they
  are equivalent for the purpose of computing limits and colimits."]
instance {α : Type*} [Preorder α] :
    (toAntisymmetrization_mono (α := α)).functor.IsEquivalence where
  full := ⟨fun f ↦ ⟨homOfLE <| by simpa using leOfHom f, rfl⟩⟩
  essSurj := Functor.essSurj_of_surj Quotient.mk_surjective

end CategoryTheory
