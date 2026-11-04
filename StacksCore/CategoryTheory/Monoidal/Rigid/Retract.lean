module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import StacksCore.CategoryTheory.Monoidal.Rigid.Lemmas

/-! # Duals of retracts

Stacks 0FFU: in a Karoubian additive monoidal category, every summand of an object which has a
left dual has a left dual.

As in `StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts`, Stacks' "`Y` is a left dual of `X`" is
Mathlib's `ExactPairing X Y`, which Mathlib names `HasRightDual X`.

Two ways in which what is proved here is more general than the tag.

* **No additivity is needed.** The argument only ever splits one idempotent, so it runs in a bare
  monoidal category that is `IsIdempotentComplete`. Stacks' hypothesis is the preadditive special
  case: for a preadditive category, "Karoubian" (every idempotent endomorphism has a kernel) is
  equivalent to `IsIdempotentComplete`, by
  `CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels`.
* **Retracts, not just summands.** A direct summand `X₁` of `X₁ ⊞ X₂` is the retract
  `⟨biprod.inl, biprod.fst⟩`, so the tag's statement is `hasRightDualBiprodFst` below.

The proof avoids the anti-isomorphism `Hom(X, X) ≅ Hom(Y, Y)ᵒᵖ` that the Stacks proof sets up.
Instead: the retract gives an idempotent `r ≫ i` on `X`; its right adjoint mate is idempotent on
`Xᘁ` because taking mates is an anti-homomorphism (`comp_rightAdjointMate`); splitting that mate
gives the dual object, and the two triangle identities come from sliding the idempotent across
the pairing with `rightAdjointMate_comp_evaluation`.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace Retract

variable {X X' : C} [HasRightDual X] (h : Retract X' X)

omit [MonoidalCategory C] [HasRightDual X] in
/-- A retract of `X` determines an idempotent endomorphism `r ≫ i` of `X`. -/
lemma idem : (h.r ≫ h.i) ≫ (h.r ≫ h.i) = h.r ≫ h.i := by simp

/-- The right adjoint mate of the idempotent determined by a retract is again idempotent,
because taking mates reverses composition. -/
lemma rightAdjointMate_idem : ((h.r ≫ h.i)ᘁ) ≫ ((h.r ≫ h.i)ᘁ) = (h.r ≫ h.i)ᘁ := by
  rw [← comp_rightAdjointMate, h.idem]

/-- Meeting the evaluation, the mate of the retract's idempotent is absorbed into `i`. -/
private lemma rightAdjointMate_tensorHom_comp_evaluation :
    (((h.r ≫ h.i)ᘁ) ⊗ₘ h.i) ≫ ε_ X (Xᘁ) = (Xᘁ : C) ◁ h.i ≫ ε_ X (Xᘁ) := by
  rw [tensorHom_def'_assoc, rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc]; simp

variable {Y' : C} (j : Y' ⟶ (Xᘁ : C)) (q : (Xᘁ : C) ⟶ Y')

/-- Meeting the evaluation, the retract's idempotent is absorbed into a section `j` of its mate. -/
private lemma tensorHom_idem_comp_evaluation (hjq : j ≫ q = 𝟙 Y') (hqj : q ≫ j = (h.r ≫ h.i)ᘁ) :
    (j ⊗ₘ (h.r ≫ h.i)) ≫ ε_ X (Xᘁ) = j ▷ X ≫ ε_ X (Xᘁ) := by
  rw [tensorHom_def_assoc, ← rightAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc,
    ← hqj, reassoc_of% hjq]

/-- A splitting of the mate idempotent turns the pairing of `X` into a pairing of the retract
`X'`. -/
@[implicit_reducible]
def exactPairing (hjq : j ≫ q = 𝟙 Y') (hqj : q ≫ j = (h.r ≫ h.i)ᘁ) : ExactPairing X' Y' where
  coevaluation' := η_ X (Xᘁ) ≫ (h.r ⊗ₘ q)
  evaluation' := (j ⊗ₘ h.i) ≫ ε_ X (Xᘁ)
  coevaluation_evaluation' := by
    rw [coevaluation_evaluation_comp, h.tensorHom_idem_comp_evaluation j q hjq hqj]
    simp [-comp_whiskerRight, whiskerRight_coevaluation_evaluation, reassoc_of% hjq]
  evaluation_coevaluation' := by
    rw [evaluation_coevaluation_comp, hqj, h.rightAdjointMate_tensorHom_comp_evaluation]
    simp [-whiskerLeft_comp, whiskerLeft_evaluation_coevaluation, reassoc_of% h.retract]

end Retract

/-- **Stacks 0FFU**: in an idempotent-complete monoidal category, a retract of an object with a
right dual has a right dual. -/
theorem nonempty_hasRightDual_of_retract [IsIdempotentComplete C] {X X' : C} [HasRightDual X]
    (h : Retract X' X) : Nonempty (HasRightDual X') := by
  obtain ⟨Y', j, q, hjq, hqj⟩ := IsIdempotentComplete.idempotents_split _ _ h.rightAdjointMate_idem
  exact ⟨{ rightDual := Y', exact := h.exactPairing j q hjq hqj }⟩

/-- **Stacks 0FFU**, as data: the right dual of a retract. -/
@[stacks 0FFU "for a retract in any idempotent-complete monoidal category", implicit_reducible]
noncomputable def hasRightDualOfRetract [IsIdempotentComplete C] {X X' : C} [HasRightDual X]
    (h : Retract X' X) : HasRightDual X' :=
  (nonempty_hasRightDual_of_retract h).some

/-- **Stacks 0FFU** in the tag's own words: a direct summand of an object which has a dual has a
dual. Stacks' "Karoubian additive" hypothesis is `[Preadditive C] [IsIdempotentComplete C]`. -/
@[stacks 0FFU, implicit_reducible]
noncomputable def hasRightDualBiprodFst [HasZeroMorphisms C] [IsIdempotentComplete C] {X₁ X₂ : C}
    [HasBinaryBiproduct X₁ X₂] [HasRightDual (X₁ ⊞ X₂)] : HasRightDual X₁ :=
  hasRightDualOfRetract ({ i := biprod.inl, r := biprod.fst } : Retract X₁ (X₁ ⊞ X₂))

end CategoryTheory
