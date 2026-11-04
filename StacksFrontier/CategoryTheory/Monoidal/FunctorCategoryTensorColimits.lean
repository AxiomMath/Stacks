module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import StacksFrontier.CategoryTheory.Monoidal.TensorRightPreservesColimits

/-!
# The pointwise tensor product on a functor category is additive and commutes with colimits

Let `J` be a category and `D` a monoidal category, so that `J ⥤ D` carries the pointwise
monoidal structure `CategoryTheory.Monoidal.functorCategoryMonoidal`. Both the tensor product
and the colimits of `J ⥤ D` are computed objectwise, so:

* if `D` is monoidal preadditive then so is `J ⥤ D`, hence `curriedTensor (J ⥤ D)` and each
  `tensorLeft F` is additive;
* if tensoring in `D` commutes with colimits of some shape, then so does tensoring in `J ⥤ D`.

## Main definitions

* `CategoryTheory.Monoidal.FunctorCategory.tensorLeftCompEvaluation` and
  `CategoryTheory.Monoidal.FunctorCategory.tensorRightCompEvaluation`: evaluating
  `F ⊗ -` (resp. `- ⊗ F`) at an object `k` of `J` is tensoring with `F.obj k` after evaluating.

## Main results

* `CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive`: `J ⥤ D` is monoidal
  preadditive when `D` is.
* `CategoryTheory.Monoidal.FunctorCategory.preservesColimitsOfShape_tensorLeft` and
  `CategoryTheory.Monoidal.FunctorCategory.preservesColimitsOfShape_tensorRight`: tensoring
  on either side in `J ⥤ D` preserves colimits of any shape that `D` has and that tensoring
  in `D` preserves.
* `CategoryTheory.Monoidal.FunctorCategory.preservesColimitsOfSize_tensorLeft`,
  `CategoryTheory.Monoidal.FunctorCategory.preservesFiniteCoproducts_tensorLeft` and their
  `tensorRight` analogues: the same for colimits of a given size and for finite coproducts.
-/

@[expose] public section

universe w w' v₁ u₁ v₂ u₂ u

namespace CategoryTheory

open Limits MonoidalCategory

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- **The pointwise monoidal structure on `J ⥤ D` is preadditive** whenever that of `D` is. -/
instance Monoidal.functorCategoryMonoidalPreadditive [Preadditive D] [MonoidalPreadditive D] :
    MonoidalPreadditive (J ⥤ D) where
  whiskerLeft_zero := by intros; ext; exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight := by intros; ext; exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add _ _ := by ext; exact MonoidalPreadditive.whiskerLeft_add _ _
  add_whiskerRight _ _ := by ext; exact MonoidalPreadditive.add_whiskerRight _ _

namespace Monoidal.FunctorCategory

/-- Evaluating `F ⊗ -` at `k : J` is the same as tensoring with `F.obj k` after evaluating
at `k`. -/
@[simps!]
def tensorLeftCompEvaluation (F : J ⥤ D) (k : J) :
    tensorLeft F ⋙ (evaluation J D).obj k ≅ (evaluation J D).obj k ⋙ tensorLeft (F.obj k) :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- Evaluating `- ⊗ F` at `k : J` is the same as tensoring with `F.obj k` after evaluating
at `k`. -/
@[simps!]
def tensorRightCompEvaluation (F : J ⥤ D) (k : J) :
    tensorRight F ⋙ (evaluation J D).obj k ≅ (evaluation J D).obj k ⋙ tensorRight (F.obj k) :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

section

variable (K : Type w) [Category.{w'} K]

/-- **Tensoring on the left in `J ⥤ D` preserves colimits of shape `K`** as soon as tensoring
on the left in `D` does and `D` has those colimits. -/
instance preservesColimitsOfShape_tensorLeft [HasColimitsOfShape K D]
    [∀ X : D, PreservesColimitsOfShape K (tensorLeft X)] (F : J ⥤ D) :
    PreservesColimitsOfShape K (tensorLeft F) :=
  preservesColimitsOfShape_of_evaluation _ _ fun k ↦
    preservesColimitsOfShape_of_natIso (tensorLeftCompEvaluation F k).symm

/-- **Tensoring on the right in `J ⥤ D` preserves colimits of shape `K`** as soon as tensoring
on the right in `D` does and `D` has those colimits. -/
instance preservesColimitsOfShape_tensorRight [HasColimitsOfShape K D]
    [∀ X : D, PreservesColimitsOfShape K (tensorRight X)] (F : J ⥤ D) :
    PreservesColimitsOfShape K (tensorRight F) :=
  preservesColimitsOfShape_of_evaluation _ _ fun k ↦
    preservesColimitsOfShape_of_natIso (tensorRightCompEvaluation F k).symm

end

/-- Tensoring on the left in `J ⥤ D` preserves colimits of size `(w', w)` as soon as tensoring
on the left in `D` does and `D` has those colimits. -/
instance preservesColimitsOfSize_tensorLeft [HasColimitsOfSize.{w', w} D]
    [∀ X : D, PreservesColimitsOfSize.{w', w} (tensorLeft X)] (F : J ⥤ D) :
    PreservesColimitsOfSize.{w', w} (tensorLeft F) where

/-- Tensoring on the right in `J ⥤ D` preserves colimits of size `(w', w)` as soon as
tensoring on the right in `D` does and `D` has those colimits. -/
instance preservesColimitsOfSize_tensorRight [HasColimitsOfSize.{w', w} D]
    [∀ X : D, PreservesColimitsOfSize.{w', w} (tensorRight X)] (F : J ⥤ D) :
    PreservesColimitsOfSize.{w', w} (tensorRight F) where

/-- Tensoring on the left in `J ⥤ D` preserves finite coproducts as soon as tensoring on the
left in `D` does and `D` has finite coproducts. -/
instance preservesFiniteCoproducts_tensorLeft [HasFiniteCoproducts D]
    [∀ X : D, PreservesFiniteCoproducts (tensorLeft X)] (F : J ⥤ D) :
    PreservesFiniteCoproducts (tensorLeft F) where
  preserves _ := inferInstance

/-- Tensoring on the right in `J ⥤ D` preserves finite coproducts as soon as tensoring on the
right in `D` does and `D` has finite coproducts. -/
instance preservesFiniteCoproducts_tensorRight [HasFiniteCoproducts D]
    [∀ X : D, PreservesFiniteCoproducts (tensorRight X)] (F : J ⥤ D) :
    PreservesFiniteCoproducts (tensorRight F) where
  preserves _ := inferInstance

end Monoidal.FunctorCategory

/-! ### Tensor conditions on graded objects in a functor category

`GradedObject.HasTensor`, `GradedObject.HasGoodTensor₁₂Tensor`,
`GradedObject.HasGoodTensorTensor₂₃` and `GradedObject.HasTensor₄ObjExt` hold for
`GradedObject I (J ⥤ D)` by typeclass inference from the corresponding hypotheses on `D`. -/

section Examples

variable (I : Type u) [AddMonoid I]

example [Preadditive D] [MonoidalPreadditive D] : (curriedTensor (J ⥤ D)).Additive :=
  inferInstance

example [Preadditive D] [MonoidalPreadditive D] (F : J ⥤ D) :
    ((curriedTensor (J ⥤ D)).obj F).Additive :=
  inferInstance

example [HasCoproducts.{u} D] (X₁ X₂ : GradedObject I (J ⥤ D)) :
    GradedObject.HasTensor X₁ X₂ :=
  inferInstance

example [HasColimitsOfSize.{u, u} D]
    [∀ X : D, PreservesColimitsOfSize.{u, u} (tensorRight X)]
    (X₁ X₂ X₃ : GradedObject I (J ⥤ D)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  inferInstance

example [HasColimitsOfSize.{u, u} D]
    [∀ X : D, PreservesColimitsOfSize.{u, u} (tensorLeft X)]
    (X₁ X₂ X₃ : GradedObject I (J ⥤ D)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  inferInstance

example [HasColimitsOfSize.{u, u} D]
    [∀ X : D, PreservesColimitsOfSize.{u, u} (tensorLeft X)]
    (X₁ X₂ X₃ X₄ : GradedObject I (J ⥤ D)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  inferInstance

example [HasInitial D] [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
    (F : J ⥤ D) :
    PreservesColimit (Functor.empty.{0} (J ⥤ D)) ((curriedTensor (J ⥤ D)).obj F) :=
  inferInstance

example [HasInitial D] [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
    (F : J ⥤ D) :
    PreservesColimit (Functor.empty.{0} (J ⥤ D)) ((curriedTensor (J ⥤ D)).flip.obj F) :=
  inferInstance

end Examples

end CategoryTheory

end
