module

public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeMate
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-!
# A square of continuous functors and a change of coefficients

Given continuous functors of sites `ug' : C₂ ⥤ C₁`, `uf : C₄ ⥤ C₂`, `uf' : C₃ ⥤ C₁`,
`ug : C₄ ⥤ C₃` and an identification `uf ⋙ ug' ≅ ug ⋙ uf'`, the pushforwards of sheaves form a
square `ug'_* ⋙ uf_* ≅ uf'_* ⋙ ug_*` (`CategoryTheory.Functor.sheafPushforwardSquare`), for any
coefficient category. Changing the coefficient category along a functor `G` commutes with
pushforwards on the nose, and with this square: this is the coherence that lets the base change
maps of the square, for coefficients `A` and for coefficients `B`, be compared.

## Main definitions

* `CategoryTheory.Functor.sheafPushforwardSquare`.

## Main results

* `CategoryTheory.Functor.sheafCompose_map_sheafPushforwardSquare_hom_app`.
* `CategoryTheory.Functor.sheafPushforwardSquare_vComp_sheafCompose`: the square identity in the
  shape consumed by `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ va ua vb ub

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃) (J₄ : GrothendieckTopology C₄)
  {ug' : C₂ ⥤ C₁} {uf : C₄ ⥤ C₂} {uf' : C₃ ⥤ C₁} {ug : C₄ ⥤ C₃}
  [ug'.IsContinuous J₂ J₁] [uf.IsContinuous J₄ J₂] [uf'.IsContinuous J₃ J₁]
  [ug.IsContinuous J₄ J₃]
  (e : uf ⋙ ug' ≅ ug ⋙ uf')

/-- The square of pushforwards `ug'_* ⋙ uf_* ≅ uf'_* ⋙ ug_*` induced by an identification
`uf ⋙ ug' ≅ ug ⋙ uf'` of the composite functors of sites. -/
def sheafPushforwardSquare (A : Type ua) [Category.{va} A] :
    ug'.sheafPushforwardContinuous A J₂ J₁ ⋙ uf.sheafPushforwardContinuous A J₄ J₂ ≅
      uf'.sheafPushforwardContinuous A J₃ J₁ ⋙ ug.sheafPushforwardContinuous A J₄ J₃ :=
  letI := isContinuous_comp uf ug' J₄ J₂ J₁
  letI := isContinuous_comp ug uf' J₄ J₃ J₁
  sheafPushforwardContinuousIso e A J₄ J₁

variable {A : Type ua} [Category.{va} A] {B : Type ub} [Category.{vb} B] (G : A ⥤ B)
  [J₁.HasSheafCompose G] [J₂.HasSheafCompose G] [J₃.HasSheafCompose G] [J₄.HasSheafCompose G]

omit [J₂.HasSheafCompose G] [J₃.HasSheafCompose G] in
/-- Changing coefficients commutes with the square of pushforwards. -/
theorem sheafCompose_map_sheafPushforwardSquare_hom_app (Z : Sheaf J₁ A) :
    (sheafCompose J₄ G).map ((sheafPushforwardSquare J₁ J₂ J₃ J₄ e A).hom.app Z) =
      (sheafPushforwardSquare J₁ J₂ J₃ J₄ e B).hom.app ((sheafCompose J₁ G).obj Z) :=
  rfl

variable [HasWeakSheafify J₁ A] [HasWeakSheafify J₂ A] [HasWeakSheafify J₃ A]
  [HasWeakSheafify J₁ B] [HasWeakSheafify J₂ B] [HasWeakSheafify J₃ B]
  [∀ P : C₂ᵒᵖ ⥤ A, ug'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]
  [∀ P : C₃ᵒᵖ ⥤ A, uf'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ A, ug.op.HasLeftKanExtension P]
  [∀ P : C₂ᵒᵖ ⥤ B, ug'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [∀ P : C₃ᵒᵖ ⥤ B, uf'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ B, ug.op.HasLeftKanExtension P]

omit [HasWeakSheafify J₁ A] [HasWeakSheafify J₂ A] [HasWeakSheafify J₃ A]
  [HasWeakSheafify J₁ B] [HasWeakSheafify J₂ B] [HasWeakSheafify J₃ B]
  [∀ P : C₂ᵒᵖ ⥤ A, ug'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]
  [∀ P : C₃ᵒᵖ ⥤ A, uf'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ A, ug.op.HasLeftKanExtension P]
  [∀ P : C₂ᵒᵖ ⥤ B, ug'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [∀ P : C₃ᵒᵖ ⥤ B, uf'.op.HasLeftKanExtension P] [∀ P : C₄ᵒᵖ ⥤ B, ug.op.HasLeftKanExtension P] in
open TwoSquare in
/-- **The square of pushforwards commutes with the change of coefficients**, in the form of the
hypothesis of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`. -/
theorem sheafPushforwardSquare_vComp_sheafCompose :
    ((TwoSquare.mk _ _ _ _ (ug'.sheafComposeSheafPushforwardIso A J₂ J₁ G).inv ≫ᵥ
        TwoSquare.mk _ _ _ _ (sheafPushforwardSquare J₁ J₂ J₃ J₄ e B).hom).whiskerRight
          (uf.sheafComposeSheafPushforwardIso A J₄ J₂ G).inv).whiskerLeft
        (uf'.sheafComposeSheafPushforwardIso A J₃ J₁ G).hom =
      TwoSquare.mk _ _ _ _ (sheafPushforwardSquare J₁ J₂ J₃ J₄ e A).hom ≫ᵥ
        TwoSquare.mk _ _ _ _ (ug.sheafComposeSheafPushforwardIso A J₄ J₃ G).inv := by
  ext Z x
  have h := congrArg (fun φ => φ.hom.app x)
    (sheafCompose_map_sheafPushforwardSquare_hom_app J₁ J₂ J₃ J₄ e G Z)
  simp only [comp_obj, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    sheafComposeSheafPushforwardIso, Iso.refl_inv, vComp, Iso.refl_hom, Category.assoc,
    NatTrans.comp_app, associator_inv_app, whiskerRight_app, NatTrans.id_app, associator_hom_app,
    whiskerLeft_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    sheafCompose_map_hom]
  change 𝟙 _ ≫ 𝟙 _ ≫ ((sheafPushforwardSquare J₁ J₂ J₃ J₄ e B).hom.app
      ((sheafCompose J₁ G).obj Z)).hom.app x ≫ 𝟙 _ =
    G.map (((sheafPushforwardSquare J₁ J₂ J₃ J₄ e A).hom.app Z).hom.app x) ≫ (𝟙 _ ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  exact h.symm

end CategoryTheory.Functor
