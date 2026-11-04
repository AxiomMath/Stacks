module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Summands of a graded tensor product

The degree-`j` part of `X₁ ⊗ X₂` is a coproduct indexed by the pairs `(i₁, i₂)` with
`i₁ + i₂ = j`. Mathlib supplies the inclusions `ιTensorObj` and the corresponding `ext`
principle; this file adds the matching projections `πTensorObj`, and the fact that a map out of
such a coproduct which kills every inclusion but one factors through that summand.

That last fact is what replaces support arguments in the graded duality results downstream: in a
triangle identity read in a fixed degree, all but one summand dies for degree reasons, so the
whole coevaluation may be replaced by a single component with no finiteness input at all.
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory GradedObject

universe w3 v3 u3

variable {I : Type w3} [AddGroup I] [DecidableEq I] {C : Type u3} [Category.{v3} C]
  [MonoidalCategory C] [Preadditive C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]

variable (X₁ X₂ X₃ : GradedObject I C)

/-- Projection of a graded tensor product onto one of its summands. -/
noncomputable def πTensorObj (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    tensorObj X₁ X₂ j ⟶ X₁ i₁ ⊗ X₂ i₂ :=
  tensorObjDesc (fun a b _ =>
    if hab : a = i₁ ∧ b = i₂ then eqToHom (by obtain ⟨rfl, rfl⟩ := hab; rfl) else 0)

@[reassoc (attr := simp)]
lemma ιTensorObj_πTensorObj_self (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj X₁ X₂ i₁ i₂ j h ≫ πTensorObj X₁ X₂ i₁ i₂ j h = 𝟙 _ := by
  simp [πTensorObj]

@[reassoc (attr := simp)]
lemma ιTensorObj_πTensorObj_ne (i₁ i₂ a b j : I) (h : a + b = j) (h' : i₁ + i₂ = j)
    (hne : ¬ (a = i₁ ∧ b = i₂)) :
    ιTensorObj X₁ X₂ a b j h ≫ πTensorObj X₁ X₂ i₁ i₂ j h' = 0 := by
  simp [πTensorObj, hne]

omit [DecidableEq I] [Preadditive C] in
/-- Right-tensoring by `X₃ i₃` keeps the universal property of the coproduct
`tensorObj X₁ X₂ j`. -/
lemma right_tensor_tensorObj_ext {A : C} [HasGoodTensor₁₂Tensor X₁ X₂ X₃] (j i₃ : I)
    (f g : tensorObj X₁ X₂ j ⊗ X₃ i₃ ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      (ιTensorObj X₁ X₂ i₁ i₂ j hi ▷ X₃ i₃) ≫ f =
        (ιTensorObj X₁ X₂ i₁ i₂ j hi ▷ X₃ i₃) ≫ g) : f = g :=
  (isColimitOfPreserves ((curriedTensor C).flip.obj (X₃ i₃))
    (isColimitCofanMapObj _ _ j)).hom_ext (by rintro ⟨⟨i₁, i₂⟩, hi⟩; exact h i₁ i₂ hi)

omit [DecidableEq I] [Preadditive C] in
/-- Left-tensoring by `X₁ i₁` keeps the universal property of the coproduct. -/
lemma left_tensor_tensorObj_ext {A : C} [HasGoodTensorTensor₂₃ X₁ X₂ X₃] (j i₁ : I)
    (f g : X₁ i₁ ⊗ tensorObj X₂ X₃ j ⟶ A)
    (h : ∀ (i₂ i₃ : I) (hi : i₂ + i₃ = j),
      (X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ j hi) ≫ f =
        (X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ j hi) ≫ g) : f = g :=
  (isColimitOfPreserves ((curriedTensor C).obj (X₁ i₁))
    (isColimitCofanMapObj _ _ j)).hom_ext (by rintro ⟨⟨i₂, i₃⟩, hi⟩; exact h i₂ i₃ hi)

variable [MonoidalPreadditive C]

/-- The left-whiskered form of the single-summand factorisation. -/
lemma eq_πTensorObj_whiskerLeft_comp {A : C} [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₂ i₃ j i₁ : I) (hj : i₂ + i₃ = j) (g : X₁ i₁ ⊗ tensorObj X₂ X₃ j ⟶ A)
    (hg : ∀ (a b : I) (hab : a + b = j), ¬ (a = i₂ ∧ b = i₃) →
      (X₁ i₁ ◁ ιTensorObj X₂ X₃ a b j hab) ≫ g = 0) :
    g = (X₁ i₁ ◁ πTensorObj X₂ X₃ i₂ i₃ j hj) ≫
      ((X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ j hj) ≫ g) := by
  refine left_tensor_tensorObj_ext X₁ X₂ X₃ j i₁ _ _ fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ | hab' := Classical.em (a = i₂ ∧ b = i₃) <;>
    simp [-whiskerLeft_comp, ← whiskerLeft_comp_assoc, *]

/-- **The structural replacement for "the coevaluation has finite support".** -/
lemma eq_πTensorObj_whiskerRight_comp {A : C} [HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (i₁ i₂ j i₃ : I) (hj : i₁ + i₂ = j) (g : tensorObj X₁ X₂ j ⊗ X₃ i₃ ⟶ A)
    (hg : ∀ (a b : I) (hab : a + b = j), ¬ (a = i₁ ∧ b = i₂) →
      (ιTensorObj X₁ X₂ a b j hab ▷ X₃ i₃) ≫ g = 0) :
    g = (πTensorObj X₁ X₂ i₁ i₂ j hj ▷ X₃ i₃) ≫
      ((ιTensorObj X₁ X₂ i₁ i₂ j hj ▷ X₃ i₃) ≫ g) := by
  refine right_tensor_tensorObj_ext X₁ X₂ X₃ j i₃ _ _ fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ | hab' := Classical.em (a = i₁ ∧ b = i₂) <;>
    simp [-comp_whiskerRight, ← comp_whiskerRight_assoc, *]

end CategoryTheory.GradedObject.Monoidal
