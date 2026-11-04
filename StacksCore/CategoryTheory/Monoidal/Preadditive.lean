module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksCore.Tactic.StacksAttribute

/-! # Additive monoidal categories

Stacks 0FNA defines an *additive monoidal category* as an additive category endowed with a
monoidal structure whose tensor product is an additive functor in each variable.

Mathlib spells this as an unbundled hypothesis block rather than a bundled structure: there is
no `AdditiveCategory` class, so Stacks' underlying additive category is `[Preadditive C]` plus
`[HasFiniteBiproducts C]`, the monoidal structure is `[MonoidalCategory C]`, and the additivity
condition is `[MonoidalPreadditive C]`. The class is stated with whiskering; the tag's literal
reading — that tensoring with a fixed object on either side is an additive functor — is
`tensorLeft_additive` and `tensorRight_additive`.

Mathlib's condition is more general than the tag, in that `MonoidalPreadditive` does not require
finite biproducts; hypotheses on lemmas in this section should ask for them only where used.
-/

@[expose] public section

add_to_stacks 0FNA "the additivity condition; the additive category is unbundled"
  CategoryTheory.MonoidalPreadditive
add_to_stacks 0FNA "`⊗` is an additive functor in the left variable"
  CategoryTheory.tensorLeft_additive
add_to_stacks 0FNA "`⊗` is an additive functor in the right variable"
  CategoryTheory.tensorRight_additive
