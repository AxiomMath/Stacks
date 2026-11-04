module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Composing coevaluations and evaluations

Technical lemmas for building new exact pairings out of old ones. In both constructions of
Stacks section 12.17 — duals of biproducts (0FFT) and duals of retracts (0FFU) — the candidate
coevaluation is an old one pushed forward along a pair of maps, and the candidate evaluation is
an old one pulled back along another pair. The two lemmas here put such a composite into a normal
form in which only one composite of those maps survives in the middle and the remaining map has
been slid out to the side; the other two extract a map whiskered onto a triangle identity.

None of this needs any additivity: these are statements about a bare monoidal category.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]
variable {Xa Ya Xb Yb X Y : C}

/-- Push a coevaluation into `X ⊗ Y` along `i` and `j`, then pull an evaluation back along `p`
and `q`: the map `j` slides out to the right and only the composite `i ≫ q` is left behind. -/
lemma coevaluation_evaluation_comp (eta : 𝟙_ C ⟶ Xa ⊗ Ya) (eps : Yb ⊗ Xb ⟶ 𝟙_ C)
    (i : Xa ⟶ X) (q : X ⟶ Xb) (j : Ya ⟶ Y) (p : Y ⟶ Yb) :
    Y ◁ (eta ≫ (i ⊗ₘ j)) ≫ (α_ Y X Y).inv ≫ ((p ⊗ₘ q) ≫ eps) ▷ Y
      = (Y ◁ eta ≫ (α_ Y Xa Ya).inv ≫ ((p ⊗ₘ (i ≫ q)) ≫ eps) ▷ Ya) ≫ 𝟙_ C ◁ j := by
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  simp only [← id_tensorHom, ← tensorHom_id, associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.comp_id,
    Category.comp_id, Category.comp_id, Category.id_comp, Category.id_comp]

/-- The mirror image of `coevaluation_evaluation_comp`: here `i` slides out to the right and
only the composite `j ≫ p` is left behind. -/
lemma evaluation_coevaluation_comp (eta : 𝟙_ C ⟶ Xa ⊗ Ya) (eps : Yb ⊗ Xb ⟶ 𝟙_ C)
    (i : Xa ⟶ X) (q : X ⟶ Xb) (j : Ya ⟶ Y) (p : Y ⟶ Yb) :
    (eta ≫ (i ⊗ₘ j)) ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ((p ⊗ₘ q) ≫ eps)
      = (eta ▷ X ≫ (α_ Xa Ya X).hom ≫ Xa ◁ (((j ≫ p) ⊗ₘ q) ≫ eps)) ≫ i ▷ 𝟙_ C := by
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  simp [← id_tensorHom, ← tensorHom_id]

variable [ExactPairing Xb Yb]

/-- A morphism `p` whiskered on the right of the coevaluation slides out of the triangle. -/
lemma whiskerRight_coevaluation_evaluation (p : Y ⟶ Yb) :
    Y ◁ η_ Xb Yb ≫ (α_ Y Xb Yb).inv ≫ ((p ▷ Xb) ≫ ε_ Xb Yb) ▷ Yb
      = p ▷ 𝟙_ C ≫ (ρ_ Yb).hom ≫ (λ_ Yb).inv := by
  rw [comp_whiskerRight, ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ExactPairing.coevaluation_evaluation]

/-- A morphism `q` whiskered on the left of the evaluation slides out of the triangle. -/
lemma whiskerLeft_evaluation_coevaluation (q : X ⟶ Xb) :
    η_ Xb Yb ▷ X ≫ (α_ Xb Yb X).hom ≫ Xb ◁ ((Yb ◁ q) ≫ ε_ Xb Yb)
      = 𝟙_ C ◁ q ≫ (λ_ Xb).hom ≫ (ρ_ Xb).inv := by
  rw [whiskerLeft_comp, ← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    ExactPairing.evaluation_coevaluation]

end CategoryTheory
