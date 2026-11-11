module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Additive categories

The Stacks project calls a category *additive* if it is preadditive and has finite products, and
restates this as: it has a zero object and direct sums. Mathlib has no class of additive
categories; it expresses additivity by the pair of instances `[Preadditive C]
[HasFiniteBiproducts C]`. This file proves that, in a preadditive category, the three conditions
agree.

## Main results

* `CategoryTheory.Limits.Preadditive.tfae_hasFiniteProducts`: in a preadditive category, having
  finite products, having finite biproducts, and having a zero object and binary biproducts are
  equivalent.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits.Preadditive

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- In a preadditive category, having finite products, having finite biproducts (direct sums),
and having a zero object and binary biproducts are equivalent. So the additive categories of the
Stacks project, the preadditive categories with finite products, are exactly the categories with
Mathlib's instances `[Preadditive C] [HasFiniteBiproducts C]`. -/
@[stacks 0104 "A preadditive category has finite products if and only if it has finite direct sums,
  if and only if it has a zero object and binary direct sums. Mathlib has no `Additive` class: an
  additive category is a category with `[Preadditive C] [HasFiniteBiproducts C]`."]
theorem tfae_hasFiniteProducts :
    List.TFAE [HasFiniteProducts C, HasFiniteBiproducts C,
      HasZeroObject C ∧ HasBinaryBiproducts C] := by
  tfae_have 1 → 2 := fun _ => HasFiniteBiproducts.of_hasFiniteProducts
  tfae_have 2 → 3 := fun _ => ⟨inferInstance, hasBinaryBiproducts_of_finite_biproducts C⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ => hasFiniteProducts_of_has_binary_and_terminal
  tfae_finish

end CategoryTheory.Limits.Preadditive
