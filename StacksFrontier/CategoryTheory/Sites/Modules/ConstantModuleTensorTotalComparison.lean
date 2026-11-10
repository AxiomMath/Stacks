module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorCopower
public import StacksFrontier.Homology.TotalComplexTransportFinite
public import StacksFrontier.Homology.DerivedTensor.KFlatDescent
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# A linear functor commutes with tensoring by a bounded complex of projective modules

Let `G` be a `Λ`-linear functor between categories of sheaves of `Λ`-modules, `K` a complex of
sheaves and `P` a complex of `Λ`-modules. The comparisons `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)` of
`Stacks.ConstantModuleTensor.comparison` assemble, together with the comparison
`Tot(G(-)) ⟶ G(Tot(-))` of total complexes, into a morphism of complexes
`Tot(G(K) ⊗_Λ P) ⟶ G(Tot(K ⊗_Λ P))`, natural in `K`, in `G` and compatible with composition of
functors. It is an isomorphism when `P` is a bounded complex of finitely generated projective
modules.

## Main definitions

* `Stacks.ConstantModuleTensor.totalComparison`.

## Main results

* `Stacks.ConstantModuleTensor.isIso_totalComparison`.
* `Stacks.ConstantModuleTensor.totalComparison_naturality`,
  `Stacks.ConstantModuleTensor.totalComparison_natTrans`,
  `Stacks.ConstantModuleTensor.totalComparison_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {C' : Type u₂} [Category.{v₂} C'] (J' : GrothendieckTopology C')
  {Λ : Type w} [CommRing Λ] [HasSheafify J (ModuleCat.{w} Λ)] [HasSheafify J' (ModuleCat.{w} Λ)]

/-- The double complex `(p, q) ↦ K^p ⊗_Λ P^q`. -/
abbrev tensorBicomplex (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    HomologicalComplex₂ (Sheaf J (ModuleCat.{w} Λ)) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor J Λ).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K).obj P

/-- `Tot(- ⊗_Λ P)` on morphisms is `mapBifunctorMap - (𝟙 P)`. -/
theorem totRight_map_eq (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    {K K' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (φ : K ⟶ K') :
    (Stacks.DerivedTensor.totRight (sheafTensor J Λ) P).map φ =
      HomologicalComplex.mapBifunctorMap φ (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) := rfl

variable (G : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)) [G.Additive] [G.Linear Λ]

/-- The comparisons `G(K^p) ⊗_Λ P^q ⟶ G(K^p ⊗_Λ P^q)`, as a morphism of double complexes. -/
def comparisonBicomplex (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    tensorBicomplex J' ((G.mapHomologicalComplex _).obj K) P ⟶
      HomologicalComplex₂.mapBicomplex G (tensorBicomplex J K P) where
  f p :=
    { f q := comparison J J' G (K.X p) (P.X q)
      comm' q q' _ := (comparison_naturality_right J J' G (K.X p) (P.d q q')).symm }
  comm' p p' _ := by
    ext q : 1
    exact (comparison_naturality_left J J' G (K.d p p') (P.X q)).symm

/-- **The comparison `Tot(G(K) ⊗_Λ P) ⟶ G(Tot(K ⊗_Λ P))`.** -/
def totalComparison (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex _).obj K) P (sheafTensor J' Λ)
        (ComplexShape.up ℤ) ⟶
      (G.mapHomologicalComplex _).obj
        (HomologicalComplex.mapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ)) :=
  HomologicalComplex₂.total.map (comparisonBicomplex J J' G K P) (ComplexShape.up ℤ) ≫
    HomologicalComplex₂.totalMap G (tensorBicomplex J K P)

/-- The component of `totalComparison` at the summand `G(K^{i₁}) ⊗_Λ P^{i₂}` of degree `n` is the
comparison `G(K^{i₁}) ⊗_Λ P^{i₂} ⟶ G(K^{i₁} ⊗_Λ P^{i₂})` followed by `G` of the inclusion of
`K^{i₁} ⊗_Λ P^{i₂}` into `Tot(K ⊗_Λ P)^n`. -/
@[reassoc]
theorem ι_totalComparison (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (i₁ i₂ n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₁, i₂) = n) :
    HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex _).obj K) P (sheafTensor J' Λ)
        (ComplexShape.up ℤ) i₁ i₂ n h ≫ (totalComparison J J' G P K).f n =
      comparison J J' G (K.X i₁) (P.X i₂) ≫
        G.map (HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ)
          i₁ i₂ n h) := by
  change HomologicalComplex₂.ιTotal (tensorBicomplex J' ((G.mapHomologicalComplex _).obj K) P)
    (ComplexShape.up ℤ) i₁ i₂ n h ≫ (HomologicalComplex₂.total.map (comparisonBicomplex J J' G K P)
    (ComplexShape.up ℤ)).f n ≫ HomologicalComplex₂.totalMapf G (tensorBicomplex J K P) n = _
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  exact congrArg (comparison J J' G (K.X i₁) (P.X i₂) ≫ ·)
    (HomologicalComplex₂.ι_totalMapf G (tensorBicomplex J K P) n i₁ i₂ h)

/-- Morphisms out of `Tot(K ⊗_Λ P)` are determined by their restrictions to the summands. -/
private theorem hom_ext_mapBifunctor {K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    {P : CochainComplex (ModuleCat.{w} Λ) ℤ}
    {Z : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    {f g : HomologicalComplex.mapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ) ⟶ Z}
    (h : ∀ n i₁ i₂ h, HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ)
      (ComplexShape.up ℤ) i₁ i₂ n h ≫ f.f n =
        HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ) i₁ i₂ n h ≫
          g.f n) : f = g :=
  HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext (h n)

/-- The comparison is natural in the complex of sheaves. -/
@[reassoc]
theorem totalComparison_naturality (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    {K K' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (φ : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap ((G.mapHomologicalComplex _).map φ) (𝟙 P)
        (sheafTensor J' Λ) (ComplexShape.up ℤ) ≫ totalComparison J J' G P K' =
      totalComparison J J' G P K ≫ (G.mapHomologicalComplex _).map
        (HomologicalComplex.mapBifunctorMap φ (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ)) := by
  refine hom_ext_mapBifunctor _ fun n i₁ i₂ h => ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_totalComparison, ι_totalComparison_assoc,
    ← G.map_comp, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    G.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact comparison_naturality_left J J' G (φ.f i₁) (P.X i₂)

/-- The comparison is natural in the functor. -/
@[reassoc]
theorem totalComparison_natTrans (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (G' : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)) [G'.Additive] [G'.Linear Λ]
    (θ : G ⟶ G') (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    HomologicalComplex.mapBifunctorMap ((NatTrans.mapHomologicalComplex θ _).app K) (𝟙 P)
        (sheafTensor J' Λ) (ComplexShape.up ℤ) ≫ totalComparison J J' G' P K =
      totalComparison J J' G P K ≫ (NatTrans.mapHomologicalComplex θ _).app
        (HomologicalComplex.mapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ)) := by
  refine hom_ext_mapBifunctor _ fun n i₁ i₂ h => ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_totalComparison, ι_totalComparison_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    NatTrans.mapHomologicalComplex_app_f]
  rw [comparison_natTrans_assoc, θ.naturality]

/-- The comparison of a composite of functors is the composite of the comparisons. -/
theorem totalComparison_comp {C'' : Type u₃} [Category.{v₃} C''] (J'' : GrothendieckTopology C'')
    [HasSheafify J'' (ModuleCat.{w} Λ)]
    (H : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J'' (ModuleCat.{w} Λ)) [H.Additive] [H.Linear Λ]
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    totalComparison J J'' (G ⋙ H) P K =
      totalComparison J' J'' H P ((G.mapHomologicalComplex _).obj K) ≫
        (H.mapHomologicalComplex _).map (totalComparison J J' G P K) := by
  refine hom_ext_mapBifunctor _ fun n i₁ i₂ h => ?_
  rw [HomologicalComplex.comp_f, ι_totalComparison]
  change _ = HomologicalComplex.ιMapBifunctor ((H.mapHomologicalComplex _).obj
    ((G.mapHomologicalComplex _).obj K)) P (sheafTensor J'' Λ) (ComplexShape.up ℤ) i₁ i₂ n h ≫
      _ ≫ _
  rw [ι_totalComparison_assoc, Functor.mapHomologicalComplex_map_f, ← H.map_comp,
    ι_totalComparison, comparison_comp, H.map_comp, Category.assoc]
  rfl

omit [HasSheafify J' (ModuleCat.{w} Λ)] [G.Additive] [G.Linear Λ] in
/-- `Tot(𝟙 K ⊗_Λ 𝟙 P)` is the identity of `Tot(K ⊗_Λ P)`. -/
theorem mapBifunctorMap_id_id (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 K) (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) = 𝟙 _ := by
  refine hom_ext_mapBifunctor _ fun n i₁ i₂ h => ?_
  simp only [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]
  exact Category.id_comp _

omit [HasSheafify J' (ModuleCat.{w} Λ)] [G.Additive] [G.Linear Λ] in
/-- `Tot((φ ≫ φ') ⊗_Λ 𝟙 P)` is the composite of `Tot(φ ⊗_Λ 𝟙 P)` and `Tot(φ' ⊗_Λ 𝟙 P)`. -/
@[reassoc]
theorem mapBifunctorMap_comp_id {K K' K'' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (φ : K ⟶ K') (φ' : K' ⟶ K'') (P : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    HomologicalComplex.mapBifunctorMap (φ ≫ φ') (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap φ (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap φ' (𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) := by
  refine hom_ext_mapBifunctor _ fun n i₁ i₂ h => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    HomologicalComplex.comp_f, Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- The comparison of a composite of functors is the composite of the comparisons, in the form
which uses the canonical identification `(G ⋙ H)(K) ≅ H(G(K))` of complexes. -/
@[reassoc]
theorem totalComparison_compIso {C'' : Type u₃} [Category.{v₃} C'']
    (J'' : GrothendieckTopology C'') [HasSheafify J'' (ModuleCat.{w} Λ)]
    (H : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J'' (ModuleCat.{w} Λ)) [H.Additive] [H.Linear Λ]
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    totalComparison J J'' (G ⋙ H) P K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) _).inv.app
          (HomologicalComplex.mapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ)) =
      HomologicalComplex.mapBifunctorMap
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) _).inv.app K) (𝟙 P)
          (sheafTensor J'' Λ) (ComplexShape.up ℤ) ≫
        totalComparison J' J'' H P ((G.mapHomologicalComplex _).obj K) ≫
          (H.mapHomologicalComplex _).map (totalComparison J J' G P K) := by
  have h : ∀ X : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ,
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).inv.app X =
        𝟙 _ := fun X => by
    ext n
    simp [Functor.mapHomologicalComplexCompIso]
  rw [h, h, Category.comp_id]
  rw [mapBifunctorMap_id_id, Category.id_comp]
  exact totalComparison_comp J J' G J'' H P K

variable (P : CochainComplex (ModuleCat.{w} Λ) ℤ)

/-- **For a bounded complex `P` of finitely generated projective modules the comparison
`Tot(G(K) ⊗_Λ P) ⟶ G(Tot(K ⊗_Λ P))` is an isomorphism.** -/
theorem isIso_totalComparison (a b : ℤ) [P.IsStrictlyLE b] [P.IsStrictlyGE a]
    [∀ q, Module.Finite Λ (P.X q)] [∀ q, Module.Projective Λ (P.X q)]
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    IsIso (totalComparison J J' G P K) := by
  have : IsIso (comparisonBicomplex J J' G K P) := by
    have : ∀ p, IsIso ((comparisonBicomplex J J' G K P).f p) := fun p => by
      have : ∀ q, IsIso (((comparisonBicomplex J J' G K P).f p).f q) := fun q =>
        (inferInstance : IsIso (comparison J J' G (K.X p) (P.X q)))
      exact HomologicalComplex.Hom.isIso_of_components _
    exact HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (HomologicalComplex₂.total.map (comparisonBicomplex J J' G K P)
      (ComplexShape.up ℤ)) :=
    (HomologicalComplex₂.total.mapIso (asIso (comparisonBicomplex J J' G K P))
      (ComplexShape.up ℤ)).isIso_hom
  classical
  have hfin : ∀ n : ℤ, ∃ s : Finset ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n}),
      ∀ i ∉ s, IsZero (((tensorBicomplex J K P).X i.1.1).X i.1.2) := fun n => by
    refine ⟨(Finset.Icc a b).image fun q => ⟨(n - q, q), by
      change (n - q) + q = n
      omega⟩, fun i hi => ?_⟩
    have hq : i.1.2 ∉ Finset.Icc a b := fun hq => hi (Finset.mem_image.2 ⟨i.1.2, hq, by
      have h2 := i.2
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h2
      change i.1.1 + i.1.2 = n at h2
      apply Subtype.ext
      ext
      · change n - i.1.2 = i.1.1
        omega
      · rfl⟩)
    have hz : IsZero (P.X i.1.2) := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
      rcases hq with hq | hq
      · exact P.isZero_of_isStrictlyGE a _ hq
      · exact P.isZero_of_isStrictlyLE b _ hq
    exact ((sheafTensor J Λ).obj (K.X i.1.1)).map_isZero hz
  have := HomologicalComplex₂.isIso_totalMap_of_finite_support (c₁₂ := ComplexShape.up ℤ)
    G (tensorBicomplex J K P) hfin
  rw [totalComparison]
  infer_instance

end Stacks.ConstantModuleTensor
