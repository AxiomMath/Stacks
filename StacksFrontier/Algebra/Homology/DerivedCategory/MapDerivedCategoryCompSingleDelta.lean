module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# A composite of exact functors on derived categories and the boundary morphism of a sequence

Let `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₃` be exact functors of abelian categories and `e : F ⋙ G ≅ H`.
The composite `F.mapDerivedCategory ⋙ G.mapDerivedCategory` carries an object `X[0]` to `H(X)[0]`,
naturally in `X`, and it carries the boundary morphism `X₃[0] ⟶ X₁[0][1]` of a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of `C₁` to the boundary morphism of `0 → H X₁ → H X₂ → H X₃ → 0`, through
these identifications. This is `CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_singleδ` for
`F` and for `G`, followed by the naturality of the boundary morphism along `e`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryCompSingleIsoOfIso`: `(F ⋙ G)(X[0]) ≅ H(X)[0]`.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompSingleIsoOfIso_singleδ`: the boundary morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : C₁ ⥤ C₃) [hH : H.PreservesZeroMorphisms] (e : F ⋙ G ≅ H)

/-- **`(F ⋙ G)(X[0]) ≅ H(X)[0]`** for exact `F`, `G` and `e : F ⋙ G ≅ H`, naturally in `X`. -/
def mapDerivedCategoryCompSingleIsoOfIso :
    DerivedCategory.singleFunctor C₁ 0 ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      H ⋙ DerivedCategory.singleFunctor C₃ 0 :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0) G.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (G.mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e (DerivedCategory.singleFunctor C₃ 0)

omit hH in
/-- The component at `X` of `mapDerivedCategoryCompSingleIsoOfIso F G H e` is the image under
`G.mapDerivedCategory` of `(F.mapDerivedCategorySingleFunctor 0).hom.app X`, followed by
`(G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X)` and by `e.hom.app X` in degree zero. -/
theorem mapDerivedCategoryCompSingleIsoOfIso_hom_app (X : C₁) :
    (mapDerivedCategoryCompSingleIsoOfIso F G H e).hom.app X =
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
          (DerivedCategory.singleFunctor C₃ 0).map (e.hom.app X) := by
  simp [mapDerivedCategoryCompSingleIsoOfIso]

/-- The boundary morphism of a short exact sequence is carried by an exact functor `F` to that of
the image sequence, through `F.mapDerivedCategorySingleFunctor 0`. -/
private theorem mapDerivedCategory_singleδ_comp {S : ShortComplex C₁} (hS : S.ShortExact) :
    F.mapDerivedCategory.map hS.singleδ ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫ (hS.map_of_exact F).singleδ := by
  rw [← hS.mapShiftedHom_singleδ' F, Iso.hom_inv_id_app_assoc]
  simp only [ShiftedHom.map, assoc]

/-- **`F ⋙ G` carries the boundary morphism of `0 → X₁ → X₂ → X₃ → 0` to that of
`0 → H X₁ → H X₂ → H X₃ → 0`**, through
`CategoryTheory.Functor.mapDerivedCategoryCompSingleIsoOfIso`. -/
theorem mapDerivedCategoryCompSingleIsoOfIso_singleδ {S : ShortComplex C₁} (hS : S.ShortExact)
    (hT : (S.map H).ShortExact) :
    ((F.mapDerivedCategory ⋙ G.mapDerivedCategory).map hS.singleδ ≫
        ((F.mapDerivedCategory ⋙ G.mapDerivedCategory).commShiftIso (1 : ℤ)).hom.app _) ≫
        ((mapDerivedCategoryCompSingleIsoOfIso F G H e).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (mapDerivedCategoryCompSingleIsoOfIso F G H e).hom.app S.X₃ ≫ hT.singleδ := by
  have S1 := mapDerivedCategory_singleδ_comp F hS
  have S2nat := mapDerivedCategory_singleδ_comp G (hS.map_of_exact F)
  have S2 : G.mapDerivedCategory.map (hS.map_of_exact F).singleδ ≫
      (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((F ⋙ DerivedCategory.singleFunctor C₂ 0).obj S.X₁) ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj S.X₁))⟦(1 : ℤ)⟧' =
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj S.X₃) ≫
        ((hS.map_of_exact F).map_of_exact G).singleδ := S2nat
  let f : (S.map F).map G ⟶ S.map H :=
    ShortComplex.homMk (e.hom.app S.X₁) (e.hom.app S.X₂) (e.hom.app S.X₃)
      (e.hom.naturality S.f).symm (e.hom.naturality S.g).symm
  have S3 : ((hS.map_of_exact F).map_of_exact G).singleδ ≫
      ((DerivedCategory.singleFunctor C₃ 0).map (e.hom.app S.X₁))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor C₃ 0).map (e.hom.app S.X₃) ≫ hT.singleδ :=
    (ShortComplex.ShortExact.singleTriangle.map ((hS.map_of_exact F).map_of_exact G) hT f).comm₃
  have S1' := congrArg G.mapDerivedCategory.map S1
  simp only [CategoryTheory.Functor.map_comp] at S1'
  rw [mapDerivedCategoryCompSingleIsoOfIso_hom_app, mapDerivedCategoryCompSingleIsoOfIso_hom_app,
    Functor.commShiftIso_comp_hom_app]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, assoc]
  have S2a : ∀ {Z : DerivedCategory C₃} (k : _ ⟶ Z),
      G.mapDerivedCategory.map (hS.map_of_exact F).singleδ ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((F ⋙ DerivedCategory.singleFunctor C₂ 0).obj S.X₁) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj S.X₁))⟦(1 : ℤ)⟧' ≫ k =
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj S.X₃) ≫
          ((hS.map_of_exact F).map_of_exact G).singleδ ≫ k := fun k => by
    simpa only [assoc] using S2 =≫ k
  have S1a : ∀ {Z : DerivedCategory C₃} (k : _ ⟶ Z),
      G.mapDerivedCategory.map (F.mapDerivedCategory.map hS.singleδ) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C₁ 0).obj S.X₁)) ≫
        G.mapDerivedCategory.map (((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(1 : ℤ)⟧') ≫
          k =
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃) ≫
          G.mapDerivedCategory.map (hS.map_of_exact F).singleδ ≫ k := fun k => by
    simpa only [assoc] using S1' =≫ k
  rw [← Functor.commShiftIso_hom_naturality_assoc G.mapDerivedCategory, S1a, S2a, S3]

end CategoryTheory.Functor

end
