module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounitDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TrianglesComponents

/-!
# Composition of weighted trace maps on derived categories

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite morphisms with weightings `w_f` and
`w_g`, and let `Λ` be a ring. For `K` in `D(Z_étale, Λ)` the composite

`(g ∘ f)_!(g ∘ f)^{-1}K = g_! f_! f^{-1} g^{-1}K ⟶ g_! g^{-1}K ⟶ K`

of `g_! Tr_{f, w_f, g^{-1}K}` and `Tr_{g, w_g, K}` is `Tr_{g ∘ f, w_{g ∘ f}, K}`, where
`w_{g ∘ f}(x) = w_f(x) w_g(f(x))`. This is Stacks 0GL3.

## Main results

* `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_comp` — the formal statement that a
  composition law for counit-shaped transformations of exact functors derives to the
  corresponding law on derived categories.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_comp` — Stacks 0GL3.

## References

* [Stacks Project, Tag 0GL3](https://stacks.math.columbia.edu/tag/0GL3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w₀ w₁ w₂

section CompToId

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory.{w₀} C₀] [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]

/-- The counit-shaped derived transformation at the image of a cochain complex, with the
factorizations of the derived functor of the composite and of the identity cancelled. -/
public theorem NatTrans.mapDerivedCategoryCompToId_app_Q_eq (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₁)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : G ⋙ F ⟶ 𝟭 C₁) (P : CochainComplex C₁ ℤ) :
    (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P) := by
  rw [NatTrans.mapDerivedCategoryCompToId_app_Q,
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso_inv_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryFactors_inv_comp_mapDerivedCategoryIdIso_hom]
  exact congrArg (fun k => _ ≫ _ ≫ k) (Category.comp_id _)

/-- The identification of the derived functor of `F₁₂` with the composite of the derived functors
of `F₁` and `F₂`, given an isomorphism `F₁₂ ≅ F₁ ⋙ F₂` of exact functors. -/
public def mapDerivedCategoryIsoComp (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₂) (F₁₂ : C₀ ⥤ C₂)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₁₂.Additive] [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    (e : F₁₂ ≅ F₁ ⋙ F₂) :
    F₁₂.mapDerivedCategory ≅ F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      F₁₂ (F₁ ⋙ F₂) e ≪≫
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso F₁ F₂

/-- The identification `mapDerivedCategoryIsoComp` at the image of a cochain complex. -/
public theorem mapDerivedCategoryIsoComp_hom_app_Q (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₂)
    (F₁₂ : C₀ ⥤ C₂)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₁₂.Additive] [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    (e : F₁₂ ≅ F₁ ⋙ F₂) (P : CochainComplex C₀ ℤ) :
    (mapDerivedCategoryIsoComp F₁ F₂ F₁₂ e).hom.app (DerivedCategory.Q.obj P) =
      F₁₂.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
        F₂.mapDerivedCategoryFactors.inv.app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app P) := by
  simp only [mapDerivedCategoryIsoComp, Iso.trans_hom, NatTrans.comp_app,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso_hom_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]

variable (P₁ : C₀ ⥤ C₁) (P₂ : C₁ ⥤ C₂) (P₁₂ : C₀ ⥤ C₂) (S₁ : C₂ ⥤ C₁) (S₂ : C₁ ⥤ C₀)
  (S₁₂ : C₂ ⥤ C₀)
  [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [P₁₂.Additive] [PreservesFiniteLimits P₁₂] [PreservesFiniteColimits P₁₂]
  [S₁.Additive] [PreservesFiniteLimits S₁] [PreservesFiniteColimits S₁]
  [S₂.Additive] [PreservesFiniteLimits S₂] [PreservesFiniteColimits S₂]
  [S₁₂.Additive] [PreservesFiniteLimits S₁₂] [PreservesFiniteColimits S₁₂]
  (pc : P₁₂ ≅ P₁ ⋙ P₂) (c : S₁₂ ≅ S₁ ⋙ S₂)
  (T₁ : P₂ ⋙ S₁ ⟶ 𝟭 C₁) (T₂ : P₁ ⋙ S₂ ⟶ 𝟭 C₀) (T₁₂ : P₁₂ ⋙ S₁₂ ⟶ 𝟭 C₀)

/-- The composite of two counit-shaped derived transformations, through the identifications of
the derived functors of the composites. -/
public def mapDerivedCategoryCompToIdComp :
    P₁₂.mapDerivedCategory ⋙ S₁₂.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C₀) :=
  Functor.whiskerRight (mapDerivedCategoryIsoComp P₁ P₂ P₁₂ pc).hom S₁₂.mapDerivedCategory ≫
    Functor.whiskerLeft (P₁.mapDerivedCategory ⋙ P₂.mapDerivedCategory)
      (mapDerivedCategoryIsoComp S₁ S₂ S₁₂ c).hom ≫
    (Functor.whiskerLeft P₁.mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapDerivedCategoryCompToId P₂ S₁ T₁)
        S₂.mapDerivedCategory) : _ ⟶ P₁.mapDerivedCategory ⋙ S₂.mapDerivedCategory) ≫
    NatTrans.mapDerivedCategoryCompToId P₁ S₂ T₂

/-- **A composition law for counit-shaped transformations of exact functors derives.** If the
transformation `T₁₂ : P₁₂ ⋙ S₁₂ ⟶ 𝟭` is, through `P₁₂ ≅ P₁ ⋙ P₂` and `S₁₂ ≅ S₁ ⋙ S₂`, the
composite of `S₂ T₁ P₁` and `T₂`, then the same holds for the derived transformations. -/
public theorem mapDerivedCategoryCompToIdComp_eq
    (h : ∀ M, T₁₂.app M = S₁₂.map (pc.hom.app M) ≫ c.hom.app (P₂.obj (P₁.obj M)) ≫
      S₂.map (T₁.app (P₁.obj M)) ≫ T₂.app M) :
    mapDerivedCategoryCompToIdComp P₁ P₂ P₁₂ S₁ S₂ S₁₂ pc c T₁ T₂ =
      NatTrans.mapDerivedCategoryCompToId P₁₂ S₁₂ T₁₂ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₀ (ComplexShape.up ℤ)) fun P => ?_
  have nat1 : S₁₂.mapDerivedCategory.map
        (P₂.mapDerivedCategoryFactors.inv.app
          ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      S₁₂.mapDerivedCategory.map
        (P₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.inv.app P)) ≫
      (mapDerivedCategoryIsoComp S₁ S₂ S₁₂ c).hom.app
        ((P₁.mapDerivedCategory ⋙ P₂.mapDerivedCategory).obj (DerivedCategory.Q.obj P)) =
      (mapDerivedCategoryIsoComp S₁ S₂ S₁₂ c).hom.app (DerivedCategory.Q.obj
          ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        S₂.mapDerivedCategory.map (S₁.mapDerivedCategory.map
          (P₂.mapDerivedCategoryFactors.inv.app
            ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        S₂.mapDerivedCategory.map (S₁.mapDerivedCategory.map
          (P₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.inv.app P))) := by
    have h0 := (mapDerivedCategoryIsoComp S₁ S₂ S₁₂ c).hom.naturality
      (P₂.mapDerivedCategoryFactors.inv.app ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        P₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.inv.app P))
    simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc] at h0
    exact h0
  have nat2 : S₁.mapDerivedCategory.map
        (P₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.inv.app P)) ≫
      (NatTrans.mapDerivedCategoryCompToId P₂ S₁ T₁).app
        (P₁.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
      (NatTrans.mapDerivedCategoryCompToId P₂ S₁ T₁).app (DerivedCategory.Q.obj
          ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        P₁.mapDerivedCategoryFactors.inv.app P := by
    have h0 := (NatTrans.mapDerivedCategoryCompToId P₂ S₁ T₁).naturality
      (P₁.mapDerivedCategoryFactors.inv.app P)
    simp only [Functor.comp_map, Functor.id_map] at h0
    exact h0
  simp only [mapDerivedCategoryCompToIdComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, mapDerivedCategoryIsoComp_hom_app_Q,
    NatTrans.mapDerivedCategoryCompToId_app_Q_eq]
  have nat2' := congrArg S₂.mapDerivedCategory.map nat2
  simp only [CategoryTheory.Functor.map_comp] at nat2'
  have c1 : S₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.inv.app P) ≫
      S₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.hom.app P) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  refine (congrArg (fun k => S₁₂.mapDerivedCategory.map (P₁₂.mapDerivedCategoryFactors.hom.app P) ≫
    S₁₂.mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex pc (ComplexShape.up ℤ)).hom.app P)) ≫ k)
    ((reassoc_of% nat1) _)).trans ?_
  rw [mapDerivedCategoryIsoComp_hom_app_Q]
  simp only [Category.assoc]
  rw [reassoc_of% nat2', reassoc_of% c1, NatTrans.mapDerivedCategoryCompToId_app_Q_eq]
  refine congrArg (S₁₂.mapDerivedCategory.map (P₁₂.mapDerivedCategoryFactors.hom.app P) ≫ ·) ?_
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_obj]
  have key12 : S₁₂.mapDerivedCategory.map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex pc (ComplexShape.up ℤ)).hom.app P)) ≫
      S₁₂.mapDerivedCategoryFactors.hom.app ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      S₁₂.mapDerivedCategoryFactors.hom.app
        ((P₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((S₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex pc (ComplexShape.up ℤ)).hom.app P)) :=
    S₁₂.mapDerivedCategoryFactors_hom_naturality _
  rw [reassoc_of% key12]
  have key : S₂.mapDerivedCategoryFactors.inv.app
        ((S₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      S₂.mapDerivedCategory.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex T₁ (ComplexShape.up ℤ)).app
          ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      S₂.mapDerivedCategoryFactors.hom.app ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      DerivedCategory.Q.map ((S₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex T₁ (ComplexShape.up ℤ)).app
          ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :=
    (Iso.inv_comp_eq (S₂.mapDerivedCategoryFactors.app _)).2
      (S₂.mapDerivedCategoryFactors_hom_naturality _)
  rw [reassoc_of% key]
  simp only [← CategoryTheory.Functor.map_comp]
  refine congrArg (fun k => S₁₂.mapDerivedCategoryFactors.hom.app
    ((P₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫ DerivedCategory.Q.map k) ?_
  ext n : 2
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex_hom_app_f]
  exact (h (P.X n)).symm

end CompToId

end CategoryTheory

namespace Stacks.ModuleCatLift

universe w' r' u₁ v₁ u₂ v₂

variable (Λ : Type r') [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})]

/-- The morphism of abelian sheaves underlying a component of the lift of a natural isomorphism
is the component of the natural isomorphism. -/
public theorem sheafCompose_map_moduleLiftNatIso_hom_app
    (G G' : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₂ AddCommGrpCat.{w'}) [G.Additive] [G'.Additive]
    (e : G ≅ G') (F : Sheaf J₁ (ModuleCat.{w'} Λ)) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map
        ((moduleLiftNatIso Λ J₁ J₂ G G' e).hom.app F) =
      e.hom.app ((sheafCompose J₁ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj F) :=
  rfl

/-- The morphism of abelian sheaves underlying a component of the inverse of the lift of a
natural isomorphism is the component of the inverse. -/
public theorem sheafCompose_map_moduleLiftNatIso_inv_app
    (G G' : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₂ AddCommGrpCat.{w'}) [G.Additive] [G'.Additive]
    (e : G ≅ G') (F : Sheaf J₁ (ModuleCat.{w'} Λ)) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map
        ((moduleLiftNatIso Λ J₁ J₂ G G' e).inv.app F) =
      e.inv.app ((sheafCompose J₁ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj F) :=
  rfl

variable {C₀ : Type*} [Category C₀] (J₀ : GrothendieckTopology C₀)
  [J₀.HasSheafCompose (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})]

/-- The middle of `Stacks.ModuleCatLift.moduleLift_comp_counit`, read on the underlying abelian
sheaves. -/
public theorem moduleLift_comp_counit_aux
    (G₁ : Sheaf J₀ AddCommGrpCat.{w'} ⥤ Sheaf J₁ AddCommGrpCat.{w'})
    (G₂ : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₂ AddCommGrpCat.{w'})
    (H₁ : Sheaf J₂ AddCommGrpCat.{w'} ⥤ Sheaf J₁ AddCommGrpCat.{w'})
    (H₂ : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₀ AddCommGrpCat.{w'})
    (H₁₂ : Sheaf J₂ AddCommGrpCat.{w'} ⥤ Sheaf J₀ AddCommGrpCat.{w'})
    [G₁.Additive] [G₂.Additive] (c : H₁₂ ≅ H₁ ⋙ H₂)
    (t₁ : ∀ N, H₁.obj (G₂.obj N) ⟶ N) (M : Sheaf J₀ (ModuleCat.{w'} Λ)) :
    c.hom.app ((sheafCompose J₂ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj
        ((moduleLift Λ J₁ J₂ G₂).obj ((moduleLift Λ J₀ J₁ G₁).obj M))) ≫
      H₂.map (t₁ ((sheafCompose J₁ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj
        ((moduleLift Λ J₀ J₁ G₁).obj M))) =
    c.hom.app (G₂.obj (G₁.obj ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ)
        AddCommGrpCat.{w'})).obj M))) ≫
      H₂.map (t₁ (G₁.obj ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ)
        AddCommGrpCat.{w'})).obj M))) :=
  rfl

/-- **A composition law for counit-shaped maps lifts to `Λ`-coefficients.** If maps
`t : H(G N) ⟶ N` of abelian sheaves satisfy a composition law through isomorphisms
`G₁ ⋙ G₂ ≅ G₁₂` and `H₁₂ ≅ H₁ ⋙ H₂`, then so do maps of sheaves of `Λ`-modules lifting them,
through the lifted isomorphisms. -/
public theorem moduleLift_comp_counit
    (G₁ : Sheaf J₀ AddCommGrpCat.{w'} ⥤ Sheaf J₁ AddCommGrpCat.{w'})
    (G₂ : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₂ AddCommGrpCat.{w'})
    (G₁₂ : Sheaf J₀ AddCommGrpCat.{w'} ⥤ Sheaf J₂ AddCommGrpCat.{w'})
    (H₁ : Sheaf J₂ AddCommGrpCat.{w'} ⥤ Sheaf J₁ AddCommGrpCat.{w'})
    (H₂ : Sheaf J₁ AddCommGrpCat.{w'} ⥤ Sheaf J₀ AddCommGrpCat.{w'})
    (H₁₂ : Sheaf J₂ AddCommGrpCat.{w'} ⥤ Sheaf J₀ AddCommGrpCat.{w'})
    [G₁.Additive] [G₂.Additive] [G₁₂.Additive] [H₁.Additive] [H₂.Additive] [H₁₂.Additive]
    (e : G₁ ⋙ G₂ ≅ G₁₂) (c : H₁₂ ≅ H₁ ⋙ H₂)
    (e' : moduleLift Λ J₀ J₂ G₁₂ ≅ moduleLift Λ J₀ J₁ G₁ ⋙ moduleLift Λ J₁ J₂ G₂)
    (c' : moduleLift Λ J₂ J₀ H₁₂ ≅ moduleLift Λ J₂ J₁ H₁ ⋙ moduleLift Λ J₁ J₀ H₂)
    (he : ∀ N, (sheafCompose J₂ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map
      (e'.hom.app N) =
      e.inv.app ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj N))
    (hc : ∀ N, (sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map
      (c'.hom.app N) =
      c.hom.app ((sheafCompose J₂ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj N))
    (t₁ : ∀ N, H₁.obj (G₂.obj N) ⟶ N) (t₂ : ∀ N, H₂.obj (G₁.obj N) ⟶ N)
    (t₁₂ : ∀ N, H₁₂.obj (G₁₂.obj N) ⟶ N)
    (τ₁ : ∀ N, (moduleLift Λ J₂ J₁ H₁).obj ((moduleLift Λ J₁ J₂ G₂).obj N) ⟶ N)
    (τ₂ : ∀ N, (moduleLift Λ J₁ J₀ H₂).obj ((moduleLift Λ J₀ J₁ G₁).obj N) ⟶ N)
    (τ₁₂ : ∀ N, (moduleLift Λ J₂ J₀ H₁₂).obj ((moduleLift Λ J₀ J₂ G₁₂).obj N) ⟶ N)
    (h₁ : ∀ N, (sheafCompose J₁ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map (τ₁ N) =
      t₁ ((sheafCompose J₁ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj N))
    (h₂ : ∀ N, (sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map (τ₂ N) =
      t₂ ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj N))
    (h₁₂ : ∀ N, (sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map (τ₁₂ N) =
      t₁₂ ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj N))
    (hab : ∀ F, t₁₂ F = H₁₂.map (e.inv.app F) ≫ c.hom.app (G₂.obj (G₁.obj F)) ≫
      H₂.map (t₁ (G₁.obj F)) ≫ t₂ F)
    (M : Sheaf J₀ (ModuleCat.{w'} Λ)) :
    τ₁₂ M = (moduleLift Λ J₂ J₀ H₁₂).map (e'.hom.app M) ≫
      c'.hom.app ((moduleLift Λ J₁ J₂ G₂).obj ((moduleLift Λ J₀ J₁ G₁).obj M)) ≫
      (moduleLift Λ J₁ J₀ H₂).map (τ₁ ((moduleLift Λ J₀ J₁ G₁).obj M)) ≫ τ₂ M := by
  refine (sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).map_injective ?_
  simp only [CategoryTheory.Functor.map_comp, sheafCompose_map_moduleLift_map, h₁, h₂, h₁₂,
    he, hc]
  have hx := moduleLift_comp_counit_aux Λ J₁ J₂ J₀ G₁ G₂ H₁ H₂ H₁₂ c t₁ M
  have hy := congrArg (fun k => H₁₂.map (e.inv.app
    ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj M)) ≫ k ≫
      t₂ ((sheafCompose J₀ (forget₂ (ModuleCat.{w'} Λ) AddCommGrpCat.{w'})).obj M)) hx
  simp only [Category.assoc] at hy
  exact (hab _).trans hy.symm

end Stacks.ModuleCatLift

namespace AlgebraicGeometry.SmallEtale

universe u v t r

section ModuleTrace

attribute [local instance] additive_abPullback

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  {w_f : X.obj → ℤ} {w_g : Y.obj → ℤ} (hw_f : IsWeighting (B.inclusion.map f) w_f)
  (hw_g : IsWeighting (B.inclusion.map g) w_g)

/-- **The composition law for inverse images of Stacks 021J** at `Λ`-coefficients,
`(g ∘ f)^{-1} ≅ f^{-1} ∘ g^{-1}`: the lift of the abelian one. -/
public abbrev pullbackModCompIso :
    pullbackMod.{u, v, r} B Λ (f ≫ g) ≅ pullbackMod.{u, v, r} B Λ g ⋙ pullbackMod.{u, v, r} B Λ f :=
  (Stacks.ModuleCatLift.moduleLiftNatIso.{max (u + 1) v r, r} Λ
    (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B X.obj X.property)
    (abPullback.{u, max v r} B g ⋙ abPullback.{u, max v r} B f)
    (abPullback.{u, max v r} B (f ≫ g))
    (compPullbackIso.{u, max v r} B f g)).symm

/-- **The composition isomorphism of Stacks 0F6T** at `Λ`-coefficients,
`(g ∘ f)_! ≅ g_! ∘ f_!`: the lift of the abelian one. -/
public abbrev fShriekModCompIso :
    fShriekMod.{u, v, r} B Λ (f ≫ g) ≅ fShriekMod.{u, v, r} B Λ f ⋙ fShriekMod.{u, v, r} B Λ g :=
  Stacks.ModuleCatLift.moduleLiftNatIso.{max (u + 1) v r, r} Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)
    (fShriekFunctor.{u, max v r} B (f ≫ g))
    (fShriekFunctor.{u, max v r} B f ⋙ fShriekFunctor.{u, max v r} B g)
    (fShriekCompIso.{u, max v r} B f g)

omit [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The abelian sheaf map underlying `f_!φ` at `Λ`-coefficients is `f_!` of the underlying map. -/
public theorem forgetModuleSheaf_map_fShriekMod_map {M N : ModuleSheaf.{u, v, r} B X Λ}
    (φ : M ⟶ N) :
    (forgetModuleSheaf.{u, v, r} B Y Λ).map ((fShriekMod.{u, v, r} B Λ f).map φ) =
      (fShriekFunctor.{u, max v r} B f).map ((forgetModuleSheaf.{u, v, r} B X Λ).map φ) :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **The weighted traces compose, at `Λ`-coefficients.** -/
public theorem weightedTraceMod_comp (M : ModuleSheaf.{u, v, r} B Z Λ) :
    weightedTraceMod.{u, v, r} B Λ (f ≫ g) (isWeighting_comp B f g hw_f hw_g) M =
      (fShriekMod.{u, v, r} B Λ (f ≫ g)).map ((pullbackModCompIso B Λ f g).hom.app M) ≫
        (fShriekModCompIso B Λ f g).hom.app
          ((pullbackMod.{u, v, r} B Λ f).obj ((pullbackMod.{u, v, r} B Λ g).obj M)) ≫
        (fShriekMod.{u, v, r} B Λ g).map
          (weightedTraceMod.{u, v, r} B Λ f hw_f ((pullbackMod.{u, v, r} B Λ g).obj M)) ≫
        weightedTraceMod.{u, v, r} B Λ g hw_g M := by
  refine Stacks.ModuleCatLift.moduleLift_comp_counit.{max (u + 1) v r, r} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Z.obj Z.property)
    (abPullback.{u, max v r} B g) (abPullback.{u, max v r} B f) (abPullback.{u, max v r} B (f ≫ g))
    (fShriekFunctor.{u, max v r} B f) (fShriekFunctor.{u, max v r} B g)
    (fShriekFunctor.{u, max v r} B (f ≫ g)) (compPullbackIso.{u, max v r} B f g)
    (fShriekCompIso.{u, max v r} B f g) (pullbackModCompIso B Λ f g) (fShriekModCompIso B Λ f g)
    ?_ ?_ (weightedTrace.{u, max v r} B f hw_f)
    (weightedTrace.{u, max v r} B g hw_g)
    (weightedTrace.{u, max v r} B (f ≫ g) (isWeighting_comp B f g hw_f hw_g))
    (weightedTraceMod.{u, v, r} B Λ f hw_f) (weightedTraceMod.{u, v, r} B Λ g hw_g)
    (weightedTraceMod.{u, v, r} B Λ (f ≫ g) (isWeighting_comp B f g hw_f hw_g))
    ?_ ?_ ?_ ?_ M
  · exact Stacks.ModuleCatLift.sheafCompose_map_moduleLiftNatIso_inv_app.{max (u + 1) v r, r}
      Λ _ _ _ _
      (compPullbackIso.{u, max v r} B f g)
  · exact Stacks.ModuleCatLift.sheafCompose_map_moduleLiftNatIso_hom_app.{max (u + 1) v r, r}
      Λ _ _ _ _
      (fShriekCompIso.{u, max v r} B f g)
  · exact forgetModuleSheaf_map_weightedTraceMod.{u, v, r} B Λ f hw_f
  · exact forgetModuleSheaf_map_weightedTraceMod.{u, v, r} B Λ g hw_g
  · exact forgetModuleSheaf_map_weightedTraceMod.{u, v, r} B Λ (f ≫ g) _
  · intro F
    refine (weightedTrace_comp.{u, max v r} B f g hw_f hw_g F).trans ?_
    unfold compWeightedTrace
    rfl

end ModuleTrace

section Derived

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  {w_f : X.obj → ℤ} {w_g : Y.obj → ℤ} (hw_f : IsWeighting (B.inclusion.map f) w_f)
  (hw_g : IsWeighting (B.inclusion.map g) w_g)
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Z Λ)]

set_option maxHeartbeats 1600000 in
/-- **Stacks 0GL3.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite morphisms, `w_f` a
weighting of `f` and `w_g` a weighting of `g`, and `Λ` a ring. For `K` in `D(Z_étale, Λ)` the
composite
`(g ∘ f)_!(g ∘ f)^{-1}K = g_! f_! f^{-1} g^{-1}K ⟶ g_! g^{-1}K ⟶ K`
of `g_! Tr_{f, w_f, g^{-1}K}` and `Tr_{g, w_g, K}` is `Tr_{g ∘ f, w_{g ∘ f}, K}`, where
`w_{g ∘ f}(x) = w_f(x) w_g(f(x))` (a weighting of `g ∘ f` by Stacks 0GK9).

The identification `(g ∘ f)_!(g ∘ f)^{-1}K = g_! f_! f^{-1} g^{-1}K` is the derived form of the
composition laws `(g ∘ f)^{-1} ≅ f^{-1} ∘ g^{-1}` of Stacks 021J and `(g ∘ f)_! ≅ g_! ∘ f_!` of
Stacks 0F6T at `Λ`-coefficients, followed by the identification of the derived functor of a
composite with the composite of the derived functors. The trace maps are those of Stacks 0GKH,
part (3). -/
@[stacks 0GL3 "the derived trace maps compose: g_! Tr_{f,w_f,g^{-1}K} followed by \
Tr_{g,w_g,K} is Tr_{g∘f,w_{g∘f},K} for every K in D(Z_étale, Λ)"]
public theorem derivedWeightedTraceMod_comp (K : DerivedCategory (ModuleSheaf.{u, v, r} B Z Λ)) :
    (fShriekMod.{u, v, r} B Λ (f ≫ g)).mapDerivedCategory.map
        ((CategoryTheory.mapDerivedCategoryIsoComp (pullbackMod.{u, v, r} B Λ g)
          (pullbackMod.{u, v, r} B Λ f) (pullbackMod.{u, v, r} B Λ (f ≫ g))
          (pullbackModCompIso B Λ f g)).hom.app K) ≫
      (CategoryTheory.mapDerivedCategoryIsoComp (fShriekMod.{u, v, r} B Λ f)
          (fShriekMod.{u, v, r} B Λ g) (fShriekMod.{u, v, r} B Λ (f ≫ g))
          (fShriekModCompIso B Λ f g)).hom.app
        ((pullbackMod.{u, v, r} B Λ f).mapDerivedCategory.obj
          ((pullbackMod.{u, v, r} B Λ g).mapDerivedCategory.obj K)) ≫
      (fShriekMod.{u, v, r} B Λ g).mapDerivedCategory.map
        ((derivedWeightedTraceMod.{u, v, t, r} B Λ f hw_f).app
          ((pullbackMod.{u, v, r} B Λ g).mapDerivedCategory.obj K)) ≫
      (derivedWeightedTraceMod.{u, v, t, r} B Λ g hw_g).app K =
    (derivedWeightedTraceMod.{u, v, t, r} B Λ (f ≫ g) (isWeighting_comp B f g hw_f hw_g)).app K :=
  congrArg (fun α => NatTrans.app α K)
    (CategoryTheory.mapDerivedCategoryCompToIdComp_eq (pullbackMod.{u, v, r} B Λ g)
      (pullbackMod.{u, v, r} B Λ f) (pullbackMod.{u, v, r} B Λ (f ≫ g))
      (fShriekMod.{u, v, r} B Λ f) (fShriekMod.{u, v, r} B Λ g)
      (fShriekMod.{u, v, r} B Λ (f ≫ g)) (pullbackModCompIso B Λ f g)
      (fShriekModCompIso B Λ f g) (weightedTraceModTrans.{u, v, r} B Λ f hw_f)
      (weightedTraceModTrans.{u, v, r} B Λ g hw_g)
      (weightedTraceModTrans.{u, v, r} B Λ (f ≫ g) (isWeighting_comp B f g hw_f hw_g))
      (weightedTraceMod_comp B Λ f g hw_f hw_g))

end Derived

end AlgebraicGeometry.SmallEtale

end
