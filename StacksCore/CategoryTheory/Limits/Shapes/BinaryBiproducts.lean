module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import StacksCore.Tactic.StacksAttribute

/-! ## Binary biproducts.

Besides the Stacks attributions, this file has four small lemmas on `biprod.lift` and
`biprod.desc` missing from Mathlib: `biprod.lift_map`, `biprod.comp_lift`, `biprod.map_desc` and
`biprod.desc_comp`. -/

@[expose] public section

add_to_stacks 0101 CategoryTheory.Limits.biprodIso
add_to_stacks 0102 CategoryTheory.Limits.biprod
add_to_stacks 0102 CategoryTheory.Limits.biprod.inl_fst
add_to_stacks 0102 CategoryTheory.Limits.biprod.inl_snd
add_to_stacks 0102 CategoryTheory.Limits.biprod.inr_snd
add_to_stacks 0102 CategoryTheory.Limits.biprod.inr_fst
add_to_stacks 09QG CategoryTheory.Limits.kernelBiprodFstIso
add_to_stacks 09QG CategoryTheory.Limits.cokernelBiproductιIso

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace Limits

/-- A pairing followed by a biproduct of maps is the pairing of the composites. -/
@[reassoc (attr := simp)]
theorem biprod.lift_map {V W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    biprod.lift f g ≫ biprod.map h k = biprod.lift (f ≫ h) (g ≫ k) := by
  ext <;> simp

/-- A map followed by a pairing is the pairing of the composites. Like Mathlib's
`prod.comp_lift`, the reassociated variant is deliberately not a simp lemma. -/
@[simp, reassoc]
theorem biprod.comp_lift {V W X Y : C} [HasBinaryBiproduct X Y] (f : V ⟶ W) (g : W ⟶ X)
    (h : W ⟶ Y) : f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) := by
  ext <;> simp

/-- A biproduct of maps followed by a copairing is the copairing of the composites. -/
@[simp, reassoc]
theorem biprod.map_desc {V W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (h : W ⟶ Y) (k : X ⟶ Z) (f : Y ⟶ V) (g : Z ⟶ V) :
    biprod.map h k ≫ biprod.desc f g = biprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

/-- A copairing followed by a map is the copairing of the composites. -/
@[simp, reassoc]
theorem biprod.desc_comp {V W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    (h : W ⟶ V) : biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  ext <;> simp

end Limits

end CategoryTheory
