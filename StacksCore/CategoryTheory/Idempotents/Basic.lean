module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import StacksCore.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import StacksCore.CategoryTheory.Preadditive.Biproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Karoubian (idempotent complete) categories

Characterizations of idempotent completeness (being *Karoubian*, `IsIdempotentComplete`,
[Stacks, Tag 09SG](https://stacks.math.columbia.edu/tag/09SG)) for a preadditive category `C`.
These are the equivalences (1) ⇔ (2) ⇔ (3) of Lemma 12.4.2,
[Stacks, Tag 09SH](https://stacks.math.columbia.edu/tag/09SH): `C` is idempotent complete iff every
idempotent has a cokernel, iff every idempotent splits off a direct summand.

## Main results

* `isIdempotentComplete_iff_idempotents_have_cokernels` (Stacks 09SH, (1) ⇔ (2)): idempotent
  completeness is equivalent to every idempotent having a cokernel.
* `isIdempotentComplete_iff'` and `isIdempotentComplete_iff_hasBinaryProduct_proj`
  (Stacks 09SH, (1) ⇔ (3)): idempotent completeness is equivalent to every idempotent splitting
  `Z` as a binary biproduct on which it is the projection onto one summand — phrased with a
  `BinaryBicone` and with the biproduct `X ⊞ Y` respectively.
* `isIdempotentComplete_iff_hasCoequalizer_of_id_and_idempotent`: the auxiliary coequalizer form,
  equivalence with `𝟙 X` and `𝟙 X - p` having a coequalizer for every idempotent `p`.

## Tags

idempotent complete, Karoubian, pseudo-abelian, split idempotent, biproduct
-/

@[expose] public section

open CategoryTheory Limits Opposite

add_to_stacks 09SG CategoryTheory.IsIdempotentComplete

variable {C : Type*} [Category* C] [Preadditive C]

open Idempotents

theorem isIdempotentComplete_iff_hasCoequalizer_of_id_and_idempotent :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p →
       HasCoequalizer (𝟙 X) (𝟙 X - p) := by
  rw [← CategoryTheory.Idempotents.isIdempotentComplete_iff_opposite,
    CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  refine ⟨fun h X p hp ↦ hasCoequalizer_iff_hasEqualizer_op _ _|>.2 <| h (op X) (𝟙 X - p).op ?_,
    fun h X p hp ↦ ?_⟩
  · rw [← op_comp, idem_of_id_sub_idem p hp]
  · have := h X.unop (𝟙 X.unop - p.unop) (idem_of_id_sub_idem p.unop <| by rw [← unop_comp, hp])
    rwa [sub_sub_cancel, hasCoequalizer_iff_hasEqualizer_op] at this

@[stacks 09SH "(1) ↔ (2)"]
lemma isIdempotentComplete_iff_idempotents_have_cokernels :
    IsIdempotentComplete C ↔ ∀ {X : C} (p : X ⟶ X), p ≫ p = p → HasCokernel p := by
  rw [isIdempotentComplete_iff_hasCoequalizer_of_id_and_idempotent]
  refine ⟨fun h X p hp ↦ have := h X p hp; ?_, fun h X p hp ↦ ?_⟩
  · simpa [sub_sub_cancel] using Preadditive.hasCokernel_of_hasCoequalizer (𝟙 X) (𝟙 X - p)
  · have : HasCokernel (𝟙 X - (𝟙 X - p)) := by rw [sub_sub_cancel]; exact h p hp
    exact Preadditive.hasCoequalizer_of_hasCokernel (𝟙 X) (𝟙 X - p)

lemma hasBinaryBiproduct_proj_to_isIdemComplete (h : ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
      ∃ (X Y : C) (b : BinaryBicone X Y) (_ : b.IsBilimit) (e : Z ≅ b.pt),
      e.hom ≫ b.snd ≫ b.inr ≫ e.inv = p) : IsIdempotentComplete C :=
  ⟨fun Z p hp ↦ have ⟨X, Y, b, _, e, he⟩ := h Z p hp
    ⟨Y, b.inr ≫ e.inv, e.hom ≫ b.snd, by simp, by simpa⟩⟩

open Idempotents

@[stacks 09SH "(1) ↔ (3)"]
lemma isIdempotentComplete_iff' : IsIdempotentComplete C ↔
    ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
    ∃ (X Y : C) (b : BinaryBicone X Y) (_ : b.IsBilimit) (e : Z ≅ b.pt),
      e.hom ≫ b.snd ≫ b.inr ≫ e.inv = p := by
  refine ⟨fun h Z p hp ↦ ?_, hasBinaryBiproduct_proj_to_isIdemComplete⟩
  obtain ⟨Y, iY, rY, hiY, hrY⟩ := h.idempotents_split Z p hp
  obtain ⟨X, iX, rX, hiX, hrX⟩ := h.idempotents_split Z (𝟙 Z - p) (idem_of_id_sub_idem p hp)
  have htot : rX ≫ iX + rY ≫ iY = 𝟙 Z := by rw [hrX, hrY, sub_add_cancel]
  refine ⟨X, Y, _, isBinaryBilimitOfTotal (BinaryBicone.mk' hiX hiY htot) htot, Iso.refl Z, ?_⟩
  change 𝟙 Z ≫ rY ≫ iY ≫ 𝟙 Z = p
  rw [Category.id_comp, Category.comp_id]
  exact hrY

/-- The direct-sum characterisation (Stacks 09SH (3)), phrased with the biproduct `X ⊞ Y`. -/
@[stacks 09SH "(1) ↔ (3)"]
lemma isIdempotentComplete_iff_hasBinaryProduct_proj : IsIdempotentComplete C ↔
    ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
      ∃ (X Y : C) (_ : HasBinaryBiproduct X Y) (e : Z ≅ X ⊞ Y),
        e.hom ≫ biprod.snd ≫ biprod.inr ≫ e.inv = p := by
  rw [isIdempotentComplete_iff']
  congr! with Z p hp X Y
  refine ⟨fun ⟨b, hb, e, he⟩ ↦ ?_, fun ⟨_, e, he⟩ ↦
    ⟨BinaryBiproduct.bicone X Y, BinaryBiproduct.isBilimit X Y, e, he⟩⟩
  have : HasBinaryBiproduct X Y := ⟨b, hb⟩
  exact ⟨‹_›, e ≪≫ biprod.uniqueUpToIso X Y hb, by simpa using he⟩
