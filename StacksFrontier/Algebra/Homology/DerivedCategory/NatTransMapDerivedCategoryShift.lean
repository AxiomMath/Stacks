module

public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Derived forms of natural transformations: shifts, single complexes and units

Let `η : F ⟶ G` be a natural transformation of exact additive functors of abelian categories.
`CategoryTheory.NatTrans.mapDerivedCategory η : F.mapDerivedCategory ⟶ G.mapDerivedCategory`
is its derived form. This file proves:

* `CategoryTheory.NatTrans.commShift_mapDerivedCategory`: it commutes with the shift;
* `CategoryTheory.NatTrans.mapDerivedCategory_app_singleFunctor`: on a single complex it is `η`
  in degree zero, read through `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`;
* `CategoryTheory.NatTrans.mapDerivedCategory_unit_conjugate`: a square of units of
  adjunctions between exact functors, holding objectwise, holds for the derived adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The natural transformation of cochain complex functors induced by `η` commutes with the shift
by integers. -/
instance NatTrans.commShift_mapHomologicalComplex (η : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)) ℤ := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  ext K i
  simp

/-- The derived form `NatTrans.mapDerivedCategory η` commutes with the shift by integers. -/
instance NatTrans.commShift_mapDerivedCategory (η : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapDerivedCategory η) ℤ := by
  have : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) F.mapDerivedCategory).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (𝟙 _) ℤ)
  have : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ G.mapDerivedCategory) G.mapDerivedCategory).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (𝟙 _) ℤ)
  unfold NatTrans.mapDerivedCategory
  exact Stacks.DerivedCategoryComparisons.localization_liftNatTrans_commShift _ _ _ _ _ _ _

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- On the complex concentrated in degree zero on `A`, the natural transformation of cochain
complex functors induced by `η` is `η.app A` in degree zero, read through
`HomologicalComplex.singleMapHomologicalComplex`. -/
theorem NatTrans.mapHomologicalComplex_app_single (η : F ⟶ G) (A : C) :
    (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj A) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app A =
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app A ≫
      (CochainComplex.singleFunctor D 0).map (η.app A) := by
  ext j
  by_cases hj : j = 0
  · subst hj
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, HomologicalComplex.comp_f,
      mapHomologicalComplex_app_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Category.assoc]
    rw [← η.naturality_assoc]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj).eq_of_tgt _ _

/-- **The derived form of `η` on a module in degree zero is `η` in degree zero.** -/
theorem NatTrans.mapDerivedCategory_app_singleFunctor (η : F ⟶ G) (A : C) :
    (NatTrans.mapDerivedCategory η).app ((DerivedCategory.singleFunctor C 0).obj A) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app A =
      (F.mapDerivedCategorySingleFunctor 0).hom.app A ≫
        (DerivedCategory.singleFunctor D 0).map (η.app A) := by
  simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Functor.comp_obj]
  rw [NatTrans.mapDerivedCategory_app_comp_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, NatTrans.mapHomologicalComplex_app_single, Functor.map_comp_assoc]
  simp only [Category.assoc]
  congr 3
  exact (DerivedCategory.singleFunctorIsoCompQ D 0).inv.naturality (η.app A)

section Units

variable {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C} [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- **A square of units of two adjunctions between exact functors persists on derived
categories.** If `η₁ ≫ b F₁ = η₂ ≫ G₂ a` objectwise, the same holds for the derived adjunctions
and the derived forms of `a` and `b`. -/
theorem NatTrans.mapDerivedCategory_unit_conjugate (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    (a : F₂ ⟶ F₁) (b : G₁ ⟶ G₂)
    (h : ∀ X : C, adj₁.unit.app X ≫ b.app (F₁.obj X) = adj₂.unit.app X ≫ G₂.map (a.app X))
    (Y : DerivedCategory C) :
    adj₁.mapDerivedCategory.unit.app Y ≫
        (NatTrans.mapDerivedCategory b).app (F₁.mapDerivedCategory.obj Y) =
      adj₂.mapDerivedCategory.unit.app Y ≫
        G₂.mapDerivedCategory.map ((NatTrans.mapDerivedCategory a).app Y) := by
  have key : adj₁.mapDerivedCategory.unit ≫ Functor.whiskerLeft F₁.mapDerivedCategory
        (NatTrans.mapDerivedCategory b) =
      adj₂.mapDerivedCategory.unit ≫ Functor.whiskerRight (NatTrans.mapDerivedCategory a)
        G₂.mapDerivedCategory := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun X => ?_)
    have hC : (NatTrans.mapHomologicalComplex adj₁.unit (ComplexShape.up ℤ)).app X ≫
        (NatTrans.mapHomologicalComplex b (ComplexShape.up ℤ)).app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) =
        (NatTrans.mapHomologicalComplex adj₂.unit (ComplexShape.up ℤ)).app X ≫
          (G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)).app X) := by
      ext n
      exact h (X.X n)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      mapDerivedCategoryAdjunction_unit_app_Q, Category.assoc]
    have hb := (NatTrans.mapDerivedCategory b).naturality (F₁.mapDerivedCategoryFactors.inv.app X)
    simp only [Functor.comp_obj] at hb
    rw [hb, NatTrans.mapDerivedCategory_app_Q, NatTrans.mapDerivedCategory_app_Q a X]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
    simp only [Functor.map_comp]
    have hf := G₂.mapDerivedCategoryFactors.inv.naturality
      ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)).app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hf
    rw [← reassoc_of% hf, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hC]
  exact congrArg (fun τ => NatTrans.app τ Y) key

end Units

end CategoryTheory
