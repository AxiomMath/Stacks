module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# In a braided category, tensoring on the right preserves whatever tensoring on the left does

In a braided monoidal category the braiding is a natural isomorphism
`tensorLeft X ≅ tensorRight X` (`CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight`), so
the two functors preserve exactly the same colimits. This file transports colimit preservation
from `tensorLeft X` to `tensorRight X` as instances.

## Main results

* `CategoryTheory.BraidedCategory.preservesColimitsOfShape_tensorRight`,
  `CategoryTheory.BraidedCategory.preservesColimitsOfSize_tensorRight` and
  `CategoryTheory.BraidedCategory.preservesFiniteCoproducts_tensorRight`: tensoring on the
  right preserves the colimits that tensoring on the left preserves.

## Implementation notes

Only the direction `tensorLeft ⟹ tensorRight` is declared, and at low priority: the converse is
equally true, but the two together would make typeclass inference loop.
-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.BraidedCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- **Tensoring on the right preserves colimits of shape `K`** whenever tensoring on the left
does, in a braided category. -/
instance (priority := 100) preservesColimitsOfShape_tensorRight (K : Type w) [Category.{w'} K]
    (X : C) [PreservesColimitsOfShape K (tensorLeft X)] :
    PreservesColimitsOfShape K (tensorRight X) :=
  preservesColimitsOfShape_of_natIso (tensorLeftIsoTensorRight X)

/-- The `PreservesColimitsOfSize` form of
`CategoryTheory.BraidedCategory.preservesColimitsOfShape_tensorRight`. -/
instance (priority := 100) preservesColimitsOfSize_tensorRight (X : C)
    [PreservesColimitsOfSize.{w', w} (tensorLeft X)] :
    PreservesColimitsOfSize.{w', w} (tensorRight X) where

/-- The finite-coproduct form of
`CategoryTheory.BraidedCategory.preservesColimitsOfShape_tensorRight`. -/
instance (priority := 100) preservesFiniteCoproducts_tensorRight (X : C)
    [PreservesFiniteCoproducts (tensorLeft X)] :
    PreservesFiniteCoproducts (tensorRight X) where
  preserves _ := inferInstance

end CategoryTheory.BraidedCategory

end
