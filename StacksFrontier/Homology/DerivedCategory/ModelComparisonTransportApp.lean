module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# A total left derived functor read at two models, on the image of the localization

`StacksDraft.DerivedModel.leftDerivedModelIso` compares a total left derived functor taken at two
models of the source and of the target. This file records the equation pinning it: on the image of
the localization functor it is the comparison at the first model, transported, followed by the
identification of the two functors being derived.

## Main results

* `StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_comparison`
* `StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_comparison_whiskerLeft`
* `StacksDraft.DerivedModel.hInv_paste_hom_app`: the inverse square `CatCommSq.hInv` pasted with a
  square of functors, at the image of an object.
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.DerivedModel

universe v u

variable {K : Type u} [Category.{v} K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K)
  {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W] [L₂.IsLocalization W]
  {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]

/-- `leftDerivedModelIso` on the image of the localization functor: it is pinned by the two
comparisons and the identification `hF` of the two functors being derived. -/
theorem leftDerivedModelIso_hom_app_comparison
    {F₁ : K ⥤ E₁} {LF₁ : D₁ ⥤ E₁} (α₁ : L₁ ⋙ LF₁ ⟶ F₁) [LF₁.IsLeftDerivedFunctor α₁ W]
    {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ F₂) [LF₂.IsLeftDerivedFunctor α₂ W]
    (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂) (X : K) :
    (leftDerivedModelIso W α₁ α₂ hG hF).hom.app (L₁.obj X) ≫ LF₂.map (hG.hom.app X) ≫
        α₂.app X = J.map (α₁.app X) ≫ hF.hom.app X := by
  have := isLeftDerivedFunctor_comp_isEquivalence W α₂ hG
  have h := Functor.leftDerivedNatTrans_app (LF₁ ⋙ J) (G ⋙ LF₂)
    ((Functor.associator L₁ LF₁ J).inv ≫ Functor.whiskerRight α₁ J)
    (transportLeftDerivedCounit α₂ hG) W hF.hom X
  simp only [transportLeftDerivedCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp] at h
  exact h

/-- `leftDerivedModelIso_hom_app_comparison` when the two functors being derived are the same
functor followed by the two localizations. -/
theorem leftDerivedModelIso_hom_app_comparison_whiskerLeft {K' : Type*} [Category* K']
    {M₁ : K' ⥤ E₁} {M₂ : K' ⥤ E₂} (P : K ⥤ K') {LF₁ : D₁ ⥤ E₁} (α₁ : L₁ ⋙ LF₁ ⟶ P ⋙ M₁)
    [LF₁.IsLeftDerivedFunctor α₁ W] {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ P ⋙ M₂)
    [LF₂.IsLeftDerivedFunctor α₂ W] (hG : L₁ ⋙ G ≅ L₂) (e : M₁ ⋙ J ≅ M₂) (X : K) :
    (leftDerivedModelIso W α₁ α₂ hG
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P e)).hom.app (L₁.obj X) ≫
        LF₂.map (hG.hom.app X) ≫ α₂.app X =
      J.map (α₁.app X) ≫ e.hom.app (P.obj X) := by
  rw [leftDerivedModelIso_hom_app_comparison]
  simp

section Square

variable {C₁ C₂ C₃ C₄ E₁ E : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* E₁] [Category* E]

/-- The inverse square `CatCommSq.hInv` of a square whose horizontal sides are equivalences,
pasted with a square of functors, at the image of an object, up to the units. -/
theorem hInv_paste_hom_app (T : C₁ ≌ C₂) (B : C₃ ≌ C₄) (Lt : C₁ ⥤ C₃) (R : C₂ ⥤ C₄)
    (h : CatCommSq T.functor Lt R B.functor) (Lε : C₁ ⥤ E₁) (Lf : E₁ ⥤ E) (Lε' : C₃ ⥤ E)
    (rZ : Lε ⋙ Lf ≅ Lt ⋙ Lε') (Y : C₁) :
    (Functor.isoWhiskerLeft T.inverse rZ ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (CatCommSq.hInv T Lt R B h).iso Lε' ≪≫
        Functor.associator _ _ _).hom.app (T.functor.obj Y) ≫
        Lε'.map (B.inverse.map (h.iso.hom.app Y)) ≫ Lε'.map (B.unitInv.app (Lt.obj Y)) =
      Lf.map (Lε.map (T.unitInv.app Y)) ≫ rZ.hom.app Y := by
  have hn := rZ.hom.naturality (T.unitInv.app Y)
  have h2 := h.iso.hom.naturality (T.unitInv.app Y)
  simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn h2
  have hinner : B.unitIso.hom.app (Lt.obj (T.inverse.obj (T.functor.obj Y))) ≫
      B.inverse.map (h.iso.inv.app (T.inverse.obj (T.functor.obj Y))) ≫
      B.inverse.map (R.map (T.counitIso.hom.app (T.functor.obj Y))) ≫
      B.inverse.map (h.iso.hom.app Y) ≫ B.unitInv.app (Lt.obj Y) = Lt.map (T.unitInv.app Y) := by
    rw [show T.counitIso.hom.app (T.functor.obj Y) = T.functor.map (T.unitInv.app Y) from
      T.counit_app_functor Y, ← B.inverse.map_comp_assoc,
      ← B.inverse.map_comp_assoc, Category.assoc, h2, Iso.inv_hom_id_app_assoc]
    simp
  rw [hn, ← hinner]
  simp [CatCommSq.hInv_iso_hom_app]

end Square



end StacksDraft.DerivedModel
