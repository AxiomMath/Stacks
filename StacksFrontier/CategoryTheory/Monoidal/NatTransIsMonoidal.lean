module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceInverseLine
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided

/-!
# Detecting monoidal natural transformations

Three criteria for a natural transformation between lax monoidal functors to be monoidal.

* Along a strong monoidal, essentially surjective functor `L : C ⥤ D` (a monoidal localization,
  say), `τ : A ⟶ B` is monoidal as soon as its whiskering `L ◁ τ` is.
* Consequently, for functors `Φ₁, Φ₂, Φ₁₂` on localized categories which lift along the
  localizations to monoidal functors `G₁, G₂, G₁₂` by monoidal isomorphisms, a transformation
  `Φ₁ ⋙ Φ₂ ⟶ Φ₁₂` compatible with a monoidal transformation `G₁ ⋙ G₂ ⟶ G₁₂` is monoidal.
* A monoidal transformation out of a composite stays monoidal after re-seating the monoidal
  structures of the three categories (`CategoryTheory.MonoidalCategory.reseatFunctorMonoidal`).

## Main results

* `CategoryTheory.NatTrans.IsMonoidal.of_whiskerLeft`
* `CategoryTheory.NatTrans.IsMonoidal.of_comp_lifting`
* `CategoryTheory.NatTrans.IsMonoidal.reseat_comp`
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

namespace NatTrans.IsMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

/-- The tensor condition for a transformation of lax monoidal functors transports along
isomorphisms of the two arguments. -/
lemma tensor_of_iso {A B : D ⥤ E} [A.LaxMonoidal] [B.LaxMonoidal] (τ : A ⟶ B)
    {X Y X' Y' : D} (eX : X' ≅ X) (eY : Y' ≅ Y)
    (h : μ A X' Y' ≫ τ.app (X' ⊗ Y') = (τ.app X' ⊗ₘ τ.app Y') ≫ μ B X' Y') :
    μ A X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ B X Y := by
  rw [← cancel_epi (A.map eX.hom ⊗ₘ A.map eY.hom), μ_natural_assoc, τ.naturality,
    reassoc_of% h, ← μ_natural, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
    τ.naturality, τ.naturality]

/-- **A transformation is monoidal if it is so after whiskering with a strong monoidal,
essentially surjective functor.** -/
theorem of_whiskerLeft (L : C ⥤ D) [L.Monoidal] [L.EssSurj] {A B : D ⥤ E}
    [A.LaxMonoidal] [B.LaxMonoidal] (τ : A ⟶ B) [h : IsMonoidal (Functor.whiskerLeft L τ)] :
    IsMonoidal τ where
  unit := by
    have h₁ := h.unit
    simp only [Functor.LaxMonoidal.comp_ε, Functor.whiskerLeft_app, Functor.comp_obj,
      Category.assoc] at h₁
    rwa [← cancel_mono (B.map (ε L)), Category.assoc, ← τ.naturality]
  tensor X Y := by
    refine tensor_of_iso τ (L.objObjPreimageIso X) (L.objObjPreimageIso Y) ?_
    have h₁ := h.tensor (L.objPreimage X) (L.objPreimage Y)
    simp only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app, Functor.comp_obj,
      Category.assoc] at h₁
    rwa [← cancel_mono (B.map (μ L _ _)), Category.assoc, Category.assoc, ← τ.naturality]

/-- **Pseudofunctoriality of lifted monoidal structures.** Let `L₁ : C₁ ⥤ D₁` be strong monoidal
and essentially surjective, and let `Φ₁ : D₁ ⥤ D₂`, `Φ₂ : D₂ ⥤ D₃`, `Φ₁₂ : D₁ ⥤ D₃` lift along
`L₁, L₂, L₃` to `G₁, G₂, G₁₂` by monoidal isomorphisms `e₁, e₂, e₁₂`. A transformation
`c : Φ₁ ⋙ Φ₂ ⟶ Φ₁₂` which on the image of `L₁` is the monoidal transformation
`ρ : G₁ ⋙ G₂ ⟶ G₁₂`, read through the `e`'s, is monoidal. -/
theorem of_comp_lifting {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃] [MonoidalCategory C₁]
    [MonoidalCategory C₂] [MonoidalCategory C₃] [MonoidalCategory D₁] [MonoidalCategory D₂]
    [MonoidalCategory D₃] (L₁ : C₁ ⥤ D₁) [L₁.Monoidal] [L₁.EssSurj] {L₂ : C₂ ⥤ D₂}
    [L₂.LaxMonoidal] {L₃ : C₃ ⥤ D₃} [L₃.LaxMonoidal] {G₁ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
    {G₁₂ : C₁ ⥤ C₃} [G₁.LaxMonoidal] [G₂.LaxMonoidal] [G₁₂.LaxMonoidal] {Φ₁ : D₁ ⥤ D₂}
    {Φ₂ : D₂ ⥤ D₃} {Φ₁₂ : D₁ ⥤ D₃} [Φ₁.LaxMonoidal] [Φ₂.LaxMonoidal] [Φ₁₂.LaxMonoidal]
    (e₁ : L₁ ⋙ Φ₁ ≅ G₁ ⋙ L₂) [IsMonoidal e₁.hom] (e₂ : L₂ ⋙ Φ₂ ≅ G₂ ⋙ L₃)
    [IsMonoidal e₂.hom] (e₁₂ : L₁ ⋙ Φ₁₂ ≅ G₁₂ ⋙ L₃) [IsMonoidal e₁₂.hom]
    (ρ : G₁ ⋙ G₂ ⟶ G₁₂) [IsMonoidal ρ] (c : Φ₁ ⋙ Φ₂ ⟶ Φ₁₂)
    (hc : ∀ X, c.app (L₁.obj X) ≫ e₁₂.hom.app X =
      Φ₂.map (e₁.hom.app X) ≫ e₂.hom.app (G₁.obj X) ≫ L₃.map (ρ.app X)) :
    IsMonoidal c := by
  have hw : Functor.whiskerLeft L₁ c =
      (Functor.associator L₁ Φ₁ Φ₂).inv ≫ Functor.whiskerRight e₁.hom Φ₂ ≫
        (Functor.associator G₁ L₂ Φ₂).hom ≫ Functor.whiskerLeft G₁ e₂.hom ≫
          (Functor.associator G₁ G₂ L₃).inv ≫ Functor.whiskerRight ρ L₃ ≫ e₁₂.inv := by
    ext X
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp]
    rw [← cancel_mono (e₁₂.hom.app X), hc X]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have : IsMonoidal (Functor.whiskerLeft L₁ c) := hw ▸ inferInstance
  exact of_whiskerLeft L₁ c

end NatTrans.IsMonoidal

namespace MonoidalCategory

section Reseat

variable {C : Type*} [Category* C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

variable {D : Type*} [Category* D] [MonoidalCategory D] {T' : D ⥤ D ⥤ D} {U' : D}

/-- The tensorator of `reseatFunctorMonoidal`, in its lax form, is that of `F` conjugated by the
two re-seating isomorphisms. -/
lemma reseatFunctorMonoidal_μ (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') (X Y : C) :
    @Functor.LaxMonoidal.μ C _ (reseat e ε) D _ (reseat e' ε') F
        (reseatFunctorMonoidal F e ε e' ε').toLaxMonoidal X Y =
      (reseatIso e' (F.obj X) (F.obj Y)).inv ≫ Functor.LaxMonoidal.μ F X Y ≫
        F.map (reseatIso e X Y).hom := by
  change ((reseatIso e' (F.obj X) (F.obj Y)).inv ≫ Functor.LaxMonoidal.μ F X Y) ≫
    F.map (reseatIso e X Y).hom = _
  rw [Category.assoc]

end Reseat

end MonoidalCategory

namespace NatTrans.IsMonoidal

open MonoidalCategory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  {T₁ : C ⥤ C ⥤ C} {U₁ : C} {T₂ : D ⥤ D ⥤ D} {U₂ : D} {T₃ : E ⥤ E ⥤ E} {U₃ : E}

/-- **A monoidal transformation out of a composite stays monoidal after re-seating** the monoidal
structures of the three categories, each functor carrying `reseatFunctorMonoidal`. -/
theorem reseat_comp (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal]
    [H.Monoidal] (τ : F ⋙ G ⟶ H) [hτ : IsMonoidal τ] (e₁ : curriedTensor C ≅ T₁) (ε₁ : 𝟙_ C ≅ U₁)
    (e₂ : curriedTensor D ≅ T₂) (ε₂ : 𝟙_ D ≅ U₂) (e₃ : curriedTensor E ≅ T₃) (ε₃ : 𝟙_ E ≅ U₃) :
    @IsMonoidal C _ (reseat e₁ ε₁) E _ (reseat e₃ ε₃) (F ⋙ G) H τ
      (@Functor.LaxMonoidal.comp C _ (reseat e₁ ε₁) D _ (reseat e₂ ε₂) E _ (reseat e₃ ε₃) F G
        (reseatFunctorMonoidal F e₁ ε₁ e₂ ε₂).toLaxMonoidal
        (reseatFunctorMonoidal G e₂ ε₂ e₃ ε₃).toLaxMonoidal)
      (reseatFunctorMonoidal H e₁ ε₁ e₃ ε₃).toLaxMonoidal := by
  refine @IsMonoidal.mk C _ (reseat e₁ ε₁) E _ (reseat e₃ ε₃) (F ⋙ G) H τ
    (@Functor.LaxMonoidal.comp C _ (reseat e₁ ε₁) D _ (reseat e₂ ε₂) E _ (reseat e₃ ε₃) F G
      (reseatFunctorMonoidal F e₁ ε₁ e₂ ε₂).toLaxMonoidal
      (reseatFunctorMonoidal G e₂ ε₂ e₃ ε₃).toLaxMonoidal)
    (reseatFunctorMonoidal H e₁ ε₁ e₃ ε₃).toLaxMonoidal ?_ (fun X Y ↦ ?_)
  · have key : ε G ≫ G.map (ε F) ≫ G.map (F.map ε₁.hom) ≫ τ.app U₁ = ε H ≫ H.map ε₁.hom := by
      have hn := τ.naturality ε₁.hom
      have h := hτ.unit
      simp only [Functor.comp_map, Category.assoc, Functor.LaxMonoidal.comp_ε] at hn h
      rw [hn, reassoc_of% h]
    rw [@Functor.LaxMonoidal.comp_ε C _ (reseat e₁ ε₁) D _ (reseat e₂ ε₂) E _ (reseat e₃ ε₃),
      reseatFunctorMonoidal_ε, reseatFunctorMonoidal_ε, reseatFunctorMonoidal_ε]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc G ε₂.hom,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    exact congrArg (ε₃.inv ≫ ·) key
  · have key : μ G (F.obj X) (F.obj Y) ≫ G.map (μ F X Y) ≫ G.map (F.map (reseatIso e₁ X Y).hom) ≫
        τ.app ((T₁.obj X).obj Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ H X Y ≫ H.map
            (reseatIso e₁ X Y).hom := by
      have hn := τ.naturality (reseatIso e₁ X Y).hom
      have h := hτ.tensor X Y
      simp only [Functor.comp_map, Category.assoc, Functor.LaxMonoidal.comp_μ] at hn h
      rw [hn, reassoc_of% h]
    rw [@Functor.LaxMonoidal.comp_μ C _ (reseat e₁ ε₁) D _ (reseat e₂ ε₂) E _ (reseat e₃ ε₃),
      reseatFunctorMonoidal_μ, reseatFunctorMonoidal_μ, reseatFunctorMonoidal_μ, reseat_tensorHom]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc G
      (reseatIso e₂ (F.obj X) (F.obj Y)).hom, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_assoc]
    exact congrArg ((reseatIso e₃ (G.obj (F.obj X)) (G.obj (F.obj Y))).inv ≫ ·) key

end NatTrans.IsMonoidal

end CategoryTheory
