module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# A morphism out of a dual is determined by its name

Let `(A, B)` be an exact pairing in a monoidal category, with unit `η : 𝟙 ⟶ A ⊗ B` and counit
`ε : B ⊗ A ⟶ 𝟙`. The *name* of a morphism `c : B ⟶ Y` is `η ≫ A ◁ c : 𝟙 ⟶ A ⊗ Y`, and `c` is
recovered from it by contracting with `ε`:
`c = ρ⁻¹ ≫ B ◁ (η ≫ A ◁ c) ≫ α⁻¹ ≫ ε ▷ Y ≫ λ`
(`CategoryTheory.ExactPairing.eq_contract_name`). This is the triangle identity of the pairing
together with the naturality of the constraints.

## Main results

* `CategoryTheory.ExactPairing.eq_contract_name`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **A morphism out of a dual is the contraction of its name with the counit.** -/
theorem ExactPairing.eq_contract_name {A B Y : C} [ExactPairing A B] (c : B ⟶ Y) :
    c = (ρ_ B).inv ≫ B ◁ (η_ A B ≫ A ◁ c) ≫ (α_ B A Y).inv ≫ ε_ A B ▷ Y ≫ (λ_ Y).hom := by
  have h : B ◁ A ◁ c ≫ (α_ B A Y).inv ≫ ε_ A B ▷ Y ≫ (λ_ Y).hom =
      (α_ B A B).inv ≫ ε_ A B ▷ B ≫ (λ_ B).hom ≫ c := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, id_whiskerLeft]
    simp
  have h' := coevaluation_evaluation A B
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, h, ← Category.assoc (B ◁ η_ A B),
    ← Category.assoc (B ◁ η_ A B ≫ (α_ B A B).inv), Category.assoc (B ◁ η_ A B), h']
  simp

end CategoryTheory
