module

public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex

/-!
# Naturality of `F(N, -)` applied degreewise as a total complex

`HomologicalComplex.singleLeftIsoMapBifunctor` identifies `F(N, -)` applied degreewise to a
cochain complex `K` with the total complex `Tot(F(N[0], K))`. This file proves that the
identification is natural in the object `N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₁]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  {N N' : C₁} (n : N ⟶ N') (K : CochainComplex C₂ ℤ)
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N) K F (ComplexShape.up ℤ)]
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj N') K F (ComplexShape.up ℤ)]

/-- **`singleLeftIsoMapBifunctor` is natural in the object placed in degree zero**: the map
`F(n, -)` applied degreewise corresponds to the map of total complexes induced by `n[0]`. -/
@[reassoc]
theorem singleLeftIsoMapBifunctor_hom_naturality_single [(F.obj N).Additive] [(F.obj N').Additive] :
    (NatTrans.mapHomologicalComplex (F.map n) (ComplexShape.up ℤ)).app K ≫
        (singleLeftIsoMapBifunctor F N' K).hom =
      (singleLeftIsoMapBifunctor F N K).hom ≫
        mapBifunctorMap ((CochainComplex.singleFunctor C₁ 0).map n) (𝟙 K) F
          (ComplexShape.up ℤ) := by
  ext i
  simp only [singleLeftIsoMapBifunctor, Hom.isoOfComponents_hom_f, Iso.symm_hom,
    singleLeftXIso_inv, comp_f, NatTrans.mapHomologicalComplex_app_f, singleLeftι,
    Category.assoc, ι_mapBifunctorMap, id_f]
  rw [← NatTrans.comp_app_assoc, ← F.map_comp, ← NatTrans.comp_app_assoc, ← F.map_comp]
  congr 3
  · simp [CochainComplex.singleFunctor, single_map_f_self]
  · rw [CategoryTheory.Functor.map_id, Category.id_comp]

end HomologicalComplex
