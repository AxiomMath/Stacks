module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Mates of 2-squares conjugated by equivalences

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions and let `α : G ⋙ L₂ ⟶ L₁ ⋙ H` be a
2-square, with mate `θ : R₁ ⋙ G ⟶ H ⋙ R₂`.  Conjugating all functors by equivalences of the four
categories gives adjunctions between the conjugated functors and a conjugated 2-square of right
adjoints.  This file shows that the mate of the conjugated 2-square is invertible as soon as `α`
is: it is `α` pasted with two invertible 2-squares made of units of the equivalences.

## Main results

* `Stacks.CategoryTheory.isIso_mateEquiv_symm_conjugate`.
* `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso`: invertibility of a mate does not depend
  on the choice of left adjoints.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.TwoSquare

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {C' : Type u₅} {D' : Type u₆} {E' : Type u₇} {F' : Type u₈}
  [Category.{v₅} C'] [Category.{v₆} D'] [Category.{v₇} E'] [Category.{v₈} F']

/-- The mate, across the adjunctions of two equivalences, of an invertible 2-square is
invertible. -/
theorem isIso_mateEquiv_symm_equivalence {G : C ⥤ E} {H : D ⥤ F} (e₁ : C ≌ D) (e₂ : E ≌ F)
    (τ : e₁.inverse ⋙ G ⟶ H ⋙ e₂.inverse) (hτ : IsIso τ) :
    IsIso ((mateEquiv e₁.toAdjunction e₂.toAdjunction).symm (TwoSquare.mk _ _ _ _ τ)).natTrans := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun c => ?_
  simp only [mateEquiv_symm_apply, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
    Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp]
  simp only [Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit, Functor.map_id,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  have : ∀ x, IsIso (e₁.unit.app x) := fun x => inferInstanceAs (IsIso (e₁.unitIso.hom.app x))
  have : ∀ x, IsIso (e₂.counit.app x) := fun x =>
    inferInstanceAs (IsIso (e₂.counitIso.hom.app x))
  infer_instance

/-- Invertibility of a mate does not depend on the choice of left adjoints of the two right
adjoints: the mates across two pairs of adjunctions with the same right adjoints differ by the
comparisons of the left adjoints. -/
theorem isIso_mateEquiv_symm_of_isIso {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D}
    {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁) (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    (h : IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans) :
    IsIso ((mateEquiv adj₁' adj₂').symm β).natTrans := by
  rw [Stacks.CategoryTheory.mateEquiv_symm_congr_left adj₁' adj₁,
    Stacks.CategoryTheory.mateEquiv_symm_congr_right adj₁ adj₂ adj₂']
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (eC : C ≌ C') (eD : D ≌ D') (eE : E ≌ E') (eF : F ≌ F')

/-- The conjugate, by equivalences of the four categories, of a 2-square of right adjoints:
the unit of `eC` cancels the two copies of `C'` in the source and the unit of `eF` inserts the
two copies of `F'` in the target. -/
def conjugateRightTwoSquare (θ : TwoSquare R₁ H G R₂) :
    TwoSquare (eD.inverse ⋙ R₁ ⋙ eC.functor) (eD.inverse ⋙ H ⋙ eF.functor)
      (eC.inverse ⋙ G ⋙ eE.functor) (eF.inverse ⋙ R₂ ⋙ eE.functor) :=
  TwoSquare.mk _ _ _ _ <|
    Functor.whiskerLeft (eD.inverse ⋙ R₁)
        (Functor.whiskerRight eC.unitIso.inv (G ⋙ eE.functor)) ≫
      Functor.whiskerLeft eD.inverse (Functor.whiskerRight θ.natTrans eE.functor) ≫
      Functor.whiskerLeft (eD.inverse ⋙ H)
        (Functor.whiskerRight eF.unitIso.hom (R₂ ⋙ eE.functor))

/-- **The mate of a conjugated 2-square is invertible** as soon as the original 2-square of left
adjoints is: across the adjunctions conjugated by the equivalences, the mate of the conjugate
of `θ = mate α` is `α` pasted with two invertible 2-squares of units of the equivalences. -/
theorem isIso_mateEquiv_symm_conjugate (α : TwoSquare G L₁ L₂ H) (hα : IsIso α.natTrans)
    (θ : TwoSquare R₁ H G R₂) (h : mateEquiv adj₁ adj₂ α = θ) :
    IsIso ((mateEquiv ((eC.symm.toAdjunction.comp adj₁).comp eD.toAdjunction)
      ((eE.symm.toAdjunction.comp adj₂).comp eF.toAdjunction)).symm
        (conjugateRightTwoSquare eC eD eE eF θ)).natTrans := by
  let τ₁ : eC.functor ⋙ (eC.inverse ⋙ G ⋙ eE.functor) ⟶ G ⋙ eE.functor :=
    Functor.whiskerRight eC.unitIso.inv (G ⋙ eE.functor)
  let τ₃ : eD.inverse ⋙ H ⟶ (eD.inverse ⋙ H ⋙ eF.functor) ⋙ eF.inverse :=
    Functor.whiskerLeft (eD.inverse ⋙ H) eF.unitIso.hom
  let σ₁ := (mateEquiv eC.symm.toAdjunction eE.symm.toAdjunction).symm (TwoSquare.mk _ _ _ _ τ₁)
  let σ₃ := (mateEquiv eD.toAdjunction eF.toAdjunction).symm (TwoSquare.mk _ _ _ _ τ₃)
  have key : conjugateRightTwoSquare eC eD eE eF θ =
      mateEquiv ((eC.symm.toAdjunction.comp adj₁).comp eD.toAdjunction)
        ((eE.symm.toAdjunction.comp adj₂).comp eF.toAdjunction) ((σ₁ ≫ᵥ α) ≫ᵥ σ₃) := by
    rw [mateEquiv_hcomp, mateEquiv_hcomp, h]
    simp only [σ₁, σ₃, Equiv.apply_symm_apply]
    ext c
    simp [conjugateRightTwoSquare, τ₁, τ₃, TwoSquare.hComp]
  rw [key, Equiv.symm_apply_apply]
  have h₁ : IsIso σ₁.natTrans := isIso_mateEquiv_symm_equivalence eC.symm eE.symm τ₁
    (by simp only [τ₁]; infer_instance)
  have h₃ : IsIso σ₃.natTrans := isIso_mateEquiv_symm_equivalence eD eF τ₃
    (by simp only [τ₃]; infer_instance)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun c => ?_
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  infer_instance

/-- A composite of comparisons `R₁ ⋙ G ≅ P k₁`, `k₁ = k₂`, `P k₂ ≅ H ⋙ R₂` of right adjoints,
conjugated by equivalences with the middle copies cancelled by units, is the conjugate
`conjugateRightTwoSquare` of the composite. -/
theorem conjugateRightTwoSquare_comp_eqToHom {ι : Sort*} (P : ι → (D ⥤ E)) {k₁ k₂ : ι}
    (hk : k₁ = k₂) (cp₁ : R₁ ⋙ G ≅ P k₁) (cp₂ : H ⋙ R₂ ≅ P k₂) :
    (Functor.isoWhiskerLeft (eD.inverse ⋙ R₁)
          (Functor.isoWhiskerRight eC.unitIso.symm (G ⋙ eE.functor)) ≪≫
        Functor.isoWhiskerLeft eD.inverse (Functor.isoWhiskerRight cp₁ eE.functor)).hom ≫
      eqToHom (congrArg (fun k => eD.inverse ⋙ P k ⋙ eE.functor) hk) ≫
      (Functor.isoWhiskerLeft (eD.inverse ⋙ H)
          (Functor.isoWhiskerRight eF.unitIso.symm (R₂ ⋙ eE.functor)) ≪≫
        Functor.isoWhiskerLeft eD.inverse (Functor.isoWhiskerRight cp₂ eE.functor)).inv =
      (conjugateRightTwoSquare eC eD eE eF
        (TwoSquare.mk _ _ _ _ (cp₁.hom ≫ eqToHom (congrArg P hk) ≫ cp₂.inv))).natTrans := by
  subst hk
  ext c
  simp [conjugateRightTwoSquare]

end Stacks.CategoryTheory

end
