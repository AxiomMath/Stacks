module

public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex

/-!
# Naturality of `Tot(F(K, N[0])) ≅ F(-, N)(K)` in the object `N`

`HomologicalComplex.mapBifunctorSingleRightIso` identifies the total complex of `F(K, N[0])` with
the degreewise image of `K` under `F(-, N)`, naturally in `K`. This file records that the
identification is natural in `N` as well.

## Main results

* `HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_right`: naturality in `N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  (K : CochainComplex C₁ ℤ)

/-- **The identification `Tot(F(K, N[0])) ≅ F(-, N)(K)` is natural in `N`.** -/
@[reassoc]
lemma mapBifunctorSingleRightIso_hom_naturality_right {N N' : C₂}
    [(F.flip.obj N).Additive] [(F.flip.obj N').Additive]
    [HasMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]
    [HasMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N') F (ComplexShape.up ℤ)]
    (g : N ⟶ N') :
    mapBifunctorMap (𝟙 K) ((CochainComplex.singleFunctor C₂ 0).map g) F (ComplexShape.up ℤ) ≫
        (mapBifunctorSingleRightIso F K N').hom =
      (mapBifunctorSingleRightIso F K N).hom ≫
        (NatTrans.mapHomologicalComplex (F.flip.map g) (ComplexShape.up ℤ)).app K := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine mapBifunctor.hom_ext fun a b hab => ?_
  by_cases hb : b = 0
  · subst hb
    have ha : a = i := by simpa using hab
    subst ha
    have h₁ : ∀ (M : C₂) [(F.flip.obj M).Additive]
        [HasMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj M) F (ComplexShape.up ℤ)],
        ιMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj M) F (ComplexShape.up ℤ) a 0 a
            hab ≫ (mapBifunctorSingleRightIso F K M).hom.f a =
          (F.obj (K.X a)).map (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
      intro M _ _
      have h := (mapBifunctorSingleRightXIso F K M a).inv_hom_id
      rw [mapBifunctorSingleRightXIso_inv, Category.assoc] at h
      change singleRightι F K M a ≫ (mapBifunctorSingleRightXIso F K M a).hom = _
      rw [← cancel_epi ((F.obj (K.X a)).map (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv), h,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, h₁,
      reassoc_of% (h₁ N)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, NatTrans.mapHomologicalComplex_app_f, Functor.flip_map_app]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    change ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map g).f 0 ≫ _ = _
    simp [HomologicalComplex.single_map_f_self]
  · exact (isZero_obj_obj_single_obj_X_right F K N a b hb).eq_of_src _ _


end HomologicalComplex

end
