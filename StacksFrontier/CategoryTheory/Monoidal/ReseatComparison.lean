module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints

/-!
# Two re-seatings of one monoidal structure

Let `C` carry a monoidal structure and let `e₁ : curriedTensor C ≅ T₁`, `e₂ : curriedTensor C ≅ T₂`
re-seat it on two bifunctors `T₁`, `T₂`.  The composite `γ = e₁⁻¹ ≫ e₂ : T₁ ≅ T₂` carries the
associativity constraint of the first re-seated structure to that of the second.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseatComparison`: the comparison `T₁(X, Y) ⟶ T₂(X, Y)`.

## Main results

* `CategoryTheory.MonoidalCategory.reseatComparison_associator`
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T₁ T₂ : C ⥤ C ⥤ C}

/-- The comparison `T₁(X, Y) ⟶ T₂(X, Y)` of two re-seatings of one monoidal structure. -/
abbrev reseatComparison (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂) (X Y : C) :
    (T₁.obj X).obj Y ⟶ (T₂.obj X).obj Y :=
  (reseatIso e₁ X Y).inv ≫ (reseatIso e₂ X Y).hom

/-- **The comparison of two re-seatings carries one associativity constraint to the other.** -/
theorem reseatComparison_associator (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂)
    {U₁ U₂ : C} (ε₁ : 𝟙_ C ≅ U₁) (ε₂ : 𝟙_ C ≅ U₂) (X Y Z : C) :
    reseatComparison e₁ e₂ ((T₁.obj X).obj Y) Z ≫ (T₂.map (reseatComparison e₁ e₂ X Y)).app Z ≫
        (@MonoidalCategoryStruct.associator C _ (reseat e₂ ε₂).toMonoidalCategoryStruct
          X Y Z).hom =
      (@MonoidalCategoryStruct.associator C _ (reseat e₁ ε₁).toMonoidalCategoryStruct
          X Y Z).hom ≫
        reseatComparison e₁ e₂ X ((T₁.obj Y).obj Z) ≫
          (T₂.obj X).map (reseatComparison e₁ e₂ Y Z) := by
  rw [reseat_associator e₂ ε₂, reseat_associator e₁ ε₁, reseat_whiskerRight e₂,
    reseat_whiskerLeft e₂]
  simp only [reseatComparison, assoc, Iso.hom_inv_id_assoc, comp_whiskerRight,
    whiskerLeft_comp]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]
  simp

end CategoryTheory.MonoidalCategory
