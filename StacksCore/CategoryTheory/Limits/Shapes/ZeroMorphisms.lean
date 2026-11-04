module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import StacksCore.Tactic.StacksAttribute

/-! ## Zero morphisms. -/

@[expose] public section

add_to_stacks 00ZZ CategoryTheory.Limits.IsInitial.isZero
add_to_stacks 00ZZ CategoryTheory.Limits.IsTerminal.isZero
add_to_stacks 00ZZ CategoryTheory.Limits.IsZero.iff_id_eq_zero

namespace CategoryTheory

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]

/-- If `Z` is a zero object, then a morphism `α : y ⟶ z` factors through `Z` if
and only if `α = 0`. -/
@[stacks 00ZZ "part 2"]
theorem factors_through_zero_iff_eq_zero
    (Z : C) (hZ : Limits.IsZero Z) {y z : C} (α : y ⟶ z) :
    (∃ (f : y ⟶ Z) (g : Z ⟶ z), α = f ≫ g) ↔ α = 0 := by
  refine ⟨fun ⟨f, g, hα⟩ => ?_, fun h => ⟨0, 0, by rw [h, Limits.zero_comp]⟩⟩
  rw [hα, hZ.eq_of_src g 0, Limits.comp_zero]

end CategoryTheory
