module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Cancelling and regrouping tensor factors in a monoidal category

Two lemmas about a monoidal category `D`, used in the study of invertible objects and of the
multiplication on their integer tensor powers.

`cancel_tensor_right` says that whiskering on the right by an object `A` which admits a tensor
inverse — that is, for which there is an isomorphism `A ⊗ B ≅ 𝟙_ D` — is injective on
morphisms. `pairShuffle` regroups a tensor square `(A ⊗ B) ⊗ (A ⊗ B)` of a pair of objects of a
braided category as `(A ⊗ A) ⊗ (B ⊗ B)`, by braiding the inner `B ⊗ A`.

## Main definitions

* `Stacks.IntPower.pairShuffle`: the regrouping `(A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ A) ⊗ (B ⊗ B)`.

## Main results

* `Stacks.IntPower.cancel_tensor_right`: whiskering on the right by a tensor-invertible object
  is injective on morphisms.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace Stacks.IntPower

section

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- **Cancelling a tensor factor with a tensor inverse.** If `A ⊗ B ≅ 𝟙_ D` then whiskering on
the right by `A` is injective on morphisms. -/
theorem cancel_tensor_right {X Y A B : D} (e : A ⊗ B ≅ 𝟙_ D) (f g : X ⟶ Y)
    (h : f ▷ A = g ▷ A) : f = g := by
  have h' : (f ▷ A) ▷ B = (g ▷ A) ▷ B := congrArg (fun k => k ▷ B) h
  have hh (k : X ⟶ Y) :
      (k ▷ A) ▷ B ≫ (α_ Y A B).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom =
        (α_ X A B).hom ≫ X ◁ e.hom ≫ (ρ_ X).hom ≫ k := by
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  apply (cancel_epi ((α_ X A B).hom ≫ X ◁ e.hom ≫ (ρ_ X).hom)).mp
  simpa only [← hh, Category.assoc] using
    congrArg (fun k => k ≫ (α_ Y A B).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom) h'

variable [BraidedCategory D]

/-- Regrouping a tensor square of a pair: `(A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ A) ⊗ (B ⊗ B)`, by
braiding the inner `B ⊗ A`. -/
noncomputable def pairShuffle (A B : D) :
    (A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ A) ⊗ (B ⊗ B) :=
  (α_ A B (A ⊗ B)) ≪≫ whiskerLeftIso A (α_ B A B).symm ≪≫
    whiskerLeftIso A (whiskerRightIso (β_ B A) B) ≪≫
    whiskerLeftIso A (α_ A B B) ≪≫ (α_ A A (B ⊗ B)).symm

end

end Stacks.IntPower

end
