module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transport of squares to full subcategories

Let `E : A ≌ B` and `E' : A' ≌ B'` be equivalences of full subcategories, compatible with
functors `F`, `F'` of the ambient categories, and let `σ` be the square of full subcategories
induced by a square `F ⋙ L ≅ L₀ ⋙ F'` of the ambient categories. This file computes the
components of `σ` and the transport of a morphism along `E`, `E'` and `σ` in the ambient
categories.

## Main results

* `CategoryTheory.Equivalence.map_comp_eq_homEquiv_comp`: the transport of `φ : Q K ⟶ K'`
  along equivalences and a square is computed by any morphism matching `φ` through isomorphisms.
* `CategoryTheory.ObjectProperty.preimageIso_square_hom_app_hom`: the components of the induced
  square, in the ambient category.
* `CategoryTheory.ObjectProperty.map_comp_eq_homEquiv_comp_hom`: the transport, in the ambient
  categories.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Equivalence

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']

/-- A morphism `Q K ⟶ K'` transported along equivalences `E`, `E'` and an isomorphism
`σ : P ⋙ E'.functor ≅ E.functor ⋙ Q` is computed by any morphism `P X ⟶ X'` matching it through
isomorphisms `E X ≅ K`, `E' X' ≅ K'`. -/
theorem map_comp_eq_homEquiv_comp (E : A ≌ B) (E' : A' ≌ B') (P : A ⥤ A') (Q : B ⥤ B')
    (σ : P ⋙ E'.functor ≅ E.functor ⋙ Q) {K : B} {K' : B'} (φ : Q.obj K ⟶ K') {X : A} {X' : A'}
    (θ : E.functor.obj X ≅ K) (θ' : E'.functor.obj X' ≅ K') (φ₂ : P.obj X ⟶ X')
    (hkey : σ.hom.app X ≫ Q.map θ.hom ≫ φ = E'.functor.map φ₂ ≫ θ'.hom) :
    P.map (E.inverse.map θ.inv ≫ E.unitIso.inv.app X) ≫ φ₂ =
      E'.toAdjunction.homEquiv _ _ (σ.hom.app (E.inverse.obj K) ≫
        Q.map (E.counitIso.hom.app K) ≫ φ) ≫ (E'.inverse.map θ'.inv ≫ E'.unitIso.inv.app X') := by
  have hε : E.functor.map (E.inverse.map θ.inv ≫ E.unitIso.inv.app X) ≫ θ.hom =
      E.counitIso.hom.app K := by simp
  have hσ := σ.hom.naturality (E.inverse.map θ.inv ≫ E.unitIso.inv.app X)
  simp only [Functor.comp_map] at hσ
  have hρ : σ.hom.app (E.inverse.obj K) ≫ Q.map (E.counitIso.hom.app K) ≫ φ =
      E'.functor.map (P.map (E.inverse.map θ.inv ≫ E.unitIso.inv.app X) ≫ φ₂) ≫ θ'.hom := by
    rw [← hε, Q.map_comp, Category.assoc, ← reassoc_of% hσ, hkey]
    simp only [Functor.map_comp, Category.assoc]
  rw [hρ]
  simp [Adjunction.homEquiv_unit]

end CategoryTheory.Equivalence

namespace CategoryTheory.ObjectProperty

variable {D₀ D₀' D D' : Type*} [Category D₀] [Category D₀'] [Category D] [Category D']
  {pA : ObjectProperty D₀} {pA' : ObjectProperty D₀'} {pB : ObjectProperty D}
  {pB' : ObjectProperty D'}

/-- A transformation obtained by preimage along the inclusion of a full subcategory, read in the
ambient category. -/
theorem preimage_whiskeringRight_app_hom {C : Type*} [Category C] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (τ : F ⋙ P.ι ⟶ G ⋙ P.ι) (X : C) :
    ((((ObjectProperty.fullyFaithfulι P).whiskeringRight C).preimage τ).app X).hom = τ.app X :=
  NatTrans.congr_app (((ObjectProperty.fullyFaithfulι P).whiskeringRight C).map_preimage τ) X

/-- Components of the transport of a square `F ⋙ L ≅ L₀ ⋙ F'` to full subcategories through
isomorphisms `E ⋙ ι ≅ ι ⋙ F`, `E' ⋙ ι ≅ ι ⋙ F'`, read in the ambient categories. -/
theorem preimageIso_square_hom_app_hom (L₀ : D₀ ⥤ D₀')
    (hP : ∀ X : pA.FullSubcategory, pA' (L₀.obj X.obj))
    (L : D ⥤ D') (hQ : ∀ X : pB.FullSubcategory, pB' (L.obj X.obj))
    (E : pA.FullSubcategory ⥤ pB.FullSubcategory) (E' : pA'.FullSubcategory ⥤ pB'.FullSubcategory)
    (F : D₀ ⥤ D) (F' : D₀' ⥤ D') (e : E ⋙ pB.ι ≅ pA.ι ⋙ F) (e' : E' ⋙ pB'.ι ≅ pA'.ι ⋙ F')
    (sq : F ⋙ L ≅ L₀ ⋙ F')
    (σ : pA'.lift (pA.ι ⋙ L₀) hP ⋙ E' ≅ E ⋙ pB'.lift (pB.ι ⋙ L) hQ)
    (hσ : σ = ((fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e' ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (liftCompιIso _ _ _) _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ sq.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (liftCompιIso _ _ _).symm ≪≫ (Functor.associator _ _ _).symm))
    (X : pA.FullSubcategory) :
    (σ.hom.app X).hom = e'.hom.app ((pA'.lift (pA.ι ⋙ L₀) hP).obj X) ≫ sq.inv.app X.obj ≫
      L.map (e.inv.app X) := by
  subst hσ
  rw [Functor.FullyFaithful.preimageIso_hom, preimage_whiskeringRight_app_hom]
  simp [liftCompιIso]

/-- A morphism of full subcategories transported along equivalences and a square `σ` of the shape
of `preimageIso_square_hom_app_hom` is computed, in the ambient categories, by any morphism
`L₀ X ⟶ X'` matching it through isomorphisms `F X ≅ K`, `F' X' ≅ K'`. -/
theorem map_comp_eq_homEquiv_comp_hom (L₀ : D₀ ⥤ D₀')
    (hP : ∀ X : pA.FullSubcategory, pA' (L₀.obj X.obj))
    (L : D ⥤ D') (hQ : ∀ X : pB.FullSubcategory, pB' (L.obj X.obj))
    (E : pA.FullSubcategory ≌ pB.FullSubcategory) (E' : pA'.FullSubcategory ≌ pB'.FullSubcategory)
    (F : D₀ ⥤ D) (F' : D₀' ⥤ D') (e : E.functor ⋙ pB.ι ≅ pA.ι ⋙ F)
    (e' : E'.functor ⋙ pB'.ι ≅ pA'.ι ⋙ F') (sq : F ⋙ L ≅ L₀ ⋙ F')
    (σ : pA'.lift (pA.ι ⋙ L₀) hP ⋙ E'.functor ≅ E.functor ⋙ pB'.lift (pB.ι ⋙ L) hQ)
    (hσ : σ = ((fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e' ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (liftCompιIso _ _ _) _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ sq.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (liftCompιIso _ _ _).symm ≪≫ (Functor.associator _ _ _).symm))
    {K : pB.FullSubcategory} {K' : pB'.FullSubcategory}
    (φ : (pB'.lift (pB.ι ⋙ L) hQ).obj K ⟶ K') (X : pA.FullSubcategory) (X' : pA'.FullSubcategory)
    (θ₀ : F.obj X.obj ≅ K.obj) (θ₀' : F'.obj X'.obj ≅ K'.obj) (φ₂ : L₀.obj X.obj ⟶ X'.obj)
    (h : sq.inv.app X.obj ≫ L.map θ₀.hom ≫ φ.hom = F'.map φ₂ ≫ θ₀'.hom) :
    ∃ (ε : E.inverse.obj K ≅ X) (ε' : E'.inverse.obj K' ≅ X'), L₀.map ε.hom.hom ≫ φ₂ =
      (E'.toAdjunction.homEquiv _ _ (σ.hom.app (E.inverse.obj K) ≫
        (pB'.lift (pB.ι ⋙ L) hQ).map (E.counitIso.hom.app K) ≫ φ)).hom ≫ ε'.hom.hom := by
  obtain ⟨θ, hθ⟩ : ∃ θ : E.functor.obj X ≅ K, θ.hom.hom = e.hom.app X ≫ θ₀.hom :=
    ⟨(fullyFaithfulι pB).preimageIso (e.app X ≪≫ θ₀), rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : E'.functor.obj X' ≅ K', θ'.hom.hom = e'.hom.app X' ≫ θ₀'.hom :=
    ⟨(fullyFaithfulι pB').preimageIso (e'.app X' ≪≫ θ₀'), rfl⟩
  set ψ : (pA'.lift (pA.ι ⋙ L₀) hP).obj X ⟶ X' := ObjectProperty.homMk φ₂ with hψ
  have hkey : σ.hom.app X ≫ (pB'.lift (pB.ι ⋙ L) hQ).map θ.hom ≫ φ = E'.functor.map ψ ≫ θ'.hom := by
    apply ObjectProperty.hom_ext
    have hn := e'.hom.naturality ψ
    simp only [Functor.comp_map, ObjectProperty.ι_map, hψ, ObjectProperty.homMk_hom] at hn
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [preimageIso_square_hom_app_hom L₀ hP L hQ E.functor E'.functor F F' e e' sq σ hσ X]
    rw [show ((pB'.lift (pB.ι ⋙ L) hQ).map θ.hom).hom = L.map θ.hom.hom from rfl, hθ, hθ',
      reassoc_of% hn]
    simp only [Category.assoc, ← L.map_comp_assoc, Iso.inv_hom_id_app_assoc, h]
  exact ⟨E.inverse.mapIso θ.symm ≪≫ E.unitIso.symm.app X,
    E'.inverse.mapIso θ'.symm ≪≫ E'.unitIso.symm.app X',
    congrArg (fun t => t.hom) (Equivalence.map_comp_eq_homEquiv_comp E E'
      (pA'.lift (pA.ι ⋙ L₀) hP) (pB'.lift (pB.ι ⋙ L) hQ) σ φ _ _ _ hkey)⟩

end CategoryTheory.ObjectProperty
