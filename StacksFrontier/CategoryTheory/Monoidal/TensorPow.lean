module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor powers of an object

The tensor power `X^{⊗ n}` of an object `X` of a monoidal category, with `X^{⊗ 0} = 𝟙` and
`X^{⊗ (n + 1)} = X^{⊗ n} ⊗ X`.

## Main definitions

* `CategoryTheory.MonoidalCategory.tensorPow`: the tensor power `X^{⊗ n}`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor power `X^{⊗ n}` of an object of a monoidal category: `X^{⊗ 0} = 𝟙` and
`X^{⊗ (n + 1)} = X^{⊗ n} ⊗ X`. -/
def tensorPow (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => tensorPow X n ⊗ X

/-- The zeroth tensor power of `X` is the monoidal unit `𝟙_ C`. -/
@[simp]
theorem tensorPow_zero (X : C) : tensorPow X 0 = 𝟙_ C :=
  rfl

/-- The `(n + 1)`-st tensor power of `X` is `X^{⊗ n} ⊗ X`. -/
@[simp]
theorem tensorPow_succ (X : C) (n : ℕ) : tensorPow X (n + 1) = tensorPow X n ⊗ X :=
  rfl

end CategoryTheory.MonoidalCategory
