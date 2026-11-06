module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Degree one classes into a single object under an exact functor

Let `F : C ⥤ D` be an exact functor of abelian categories, `K` a cochain complex in `C` and `M`
an object of `C`. A morphism `z : K ⟶ M[0]⟦1⟧` in `D(C)` — a class in `Ext¹(K, M)` — is carried
by `F.mapDerivedCategory` to a class `F z : F K ⟶ (F M)[0]⟦1⟧` in `D(D)` (`mapExtOne`), reading
`F.mapDerivedCategory (Q K)` as `Q (F K)` and `F.mapDerivedCategory (M[0]⟦1⟧)` as `(F M)[0]⟦1⟧`.
This file computes `mapExtOne` on the classes of chain maps `K ⟶ M[-1]`, the form in which the
classes of conormal homomorphisms of naive cotangent complexes are written.

## Main definitions

* `CategoryTheory.Functor.mapExtOne`: the image of a class under an exact functor.

## Main results

* `CategoryTheory.Functor.mapExtOne_Q_map_comp`: `mapExtOne` commutes with precomposition by the
  image of a chain map.
* `CategoryTheory.Functor.mapExtOne_Q_map_shiftIso`: on the class of a chain map `K ⟶ M[-1]` it
  is the class of the image chain map `F K ⟶ (F M)[-1]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The image under an exact functor of a class `K ⟶ M[0]⟦1⟧`**, read as a class
`F K ⟶ (F M)[0]⟦1⟧`. -/
def mapExtOne {K : CochainComplex C ℤ} {M : C}
    (z : DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor C 0).obj M)⟦(1 : ℤ)⟧) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M))⟦(1 : ℤ)⟧ :=
  F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map z ≫
    (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧'

/-- `mapExtOne` commutes with precomposition by the image of a chain map. -/
theorem mapExtOne_Q_map_comp {K L : CochainComplex C ℤ} {M : C} (φ : K ⟶ L)
    (z : DerivedCategory.Q.obj L ⟶ ((DerivedCategory.singleFunctor C 0).obj M)⟦(1 : ℤ)⟧) :
    F.mapExtOne (DerivedCategory.Q.map φ ≫ z) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
        F.mapExtOne z := by
  simp only [mapExtOne, Functor.map_comp, Category.assoc]
  exact (F.mapDerivedCategoryFactors.inv.naturality_assoc φ _).symm

omit [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- The chain-level identity behind `mapDerivedCategory_map_singleShiftIso_inv`. -/
theorem mapHomologicalComplex_map_singleShiftIso_inv (M : C) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app M)⟦(1 : ℤ)⟧' =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (-1)).hom.app M ≫
        ((CochainComplex.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
          (F.obj M) := by
  rw [← cancel_epi ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ)
    (-1)).inv.app M), Iso.inv_hom_id_app_assoc]
  refine HomologicalComplex.from_single_hom_ext ?_
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleMapHomologicalComplex,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, eqToHom_map]

/-- The shift comparison of the single functors of `D(A)` is that of chain complexes, up to the
commutation of `Q` with the shift. -/
private theorem singleFunctors_shiftIso_inv_app {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (M : A) :
    ((DerivedCategory.singleFunctors A).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M =
      DerivedCategory.Q.map (((CochainComplex.singleFunctors A).shiftIso (1 : ℤ) (-1) 0
        (by decide)).inv.app M) ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) := by
  simp [DerivedCategory.singleFunctors, SingleFunctors.postcomp]

/-- `mapDerivedCategorySingleFunctor` is `mapDerivedCategoryFactors` followed by the image of the
comparison of single complexes. -/
private theorem mapDerivedCategorySingleFunctor_hom_app_eq (n : ℤ) (M : C) :
    (F.mapDerivedCategorySingleFunctor n).hom.app M =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj
        M) ≫ DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app M) := by
  simp only [comp_obj, mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
    isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
    associator_hom_app, whiskerLeft_app, associator_inv_app, DerivedCategory.Q_obj_single_obj,
    whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
  exact Category.id_comp _

/-- The shift comparison of the single functors of `D(C)` in degrees `-1` and `0`, on chain
complexes. -/
theorem mapDerivedCategory_map_singleShiftIso_inv (M : C) :
    F.mapDerivedCategory.map (((DerivedCategory.singleFunctors C).shiftIso (1 : ℤ) (-1) 0
        (by decide)).inv.app M) ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor (-1)).hom.app M ≫
        ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
          (F.obj M) := by
  have hc := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom (1 : ℤ)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hc
  have hd := congrArg DerivedCategory.Q.map (F.mapHomologicalComplex_map_singleShiftIso_inv M)
  simp only [Functor.map_comp] at hd
  have hQ : DerivedCategory.Q.map
        (((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app M)⟦(1 : ℤ)⟧') ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (F.obj M)) =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)) ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app M))⟦(1 : ℤ)⟧' :=
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app M)
  have hn : F.mapDerivedCategory.map (DerivedCategory.Q.map
        (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M)) ≫
      F.mapDerivedCategoryFactors.hom.app ((shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)) =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M)) :=
    F.mapDerivedCategoryFactors_hom_naturality
      (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M)
  calc _ = F.mapDerivedCategory.map (DerivedCategory.Q.map
          (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M)) ≫
        (F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)) ≫
        (F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))⟦(1 : ℤ)⟧') ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app M))⟦(1 : ℤ)⟧' := by
        rw [singleFunctors_shiftIso_inv_app, F.mapDerivedCategorySingleFunctor_hom_app_eq]
        simp only [Functor.map_comp, Category.assoc]
        rfl
    _ = _ := by
        rw [hc]
        simp only [Category.assoc]
        rw [reassoc_of% hn, ← hQ, singleFunctors_shiftIso_inv_app,
          F.mapDerivedCategorySingleFunctor_hom_app_eq]
        simp only [Category.assoc]
        congr 1
        have hd' := congrArg (· ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (F.obj M))) hd
        simp only [Category.assoc] at hd'
        exact hd'


/-- **On the class of a chain map `K ⟶ M[-1]`, `mapExtOne` is the class of the image chain map
`F K ⟶ (F M)[-1]`.** -/
theorem mapExtOne_Q_map_shiftIso {K : CochainComplex C ℤ} {M : C}
    (ψ : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M) :
    F.mapExtOne (DerivedCategory.Q.map ψ ≫
        ((DerivedCategory.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
          (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (-1)).hom.app M) ≫
        ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
          (F.obj M) := by
  simp only [mapExtOne, Functor.map_comp, Category.assoc]
  rw [F.mapDerivedCategory_map_singleShiftIso_inv M,
    F.mapDerivedCategorySingleFunctor_hom_app_eq, Category.assoc,
    F.mapDerivedCategoryFactors_hom_naturality_assoc ψ, Iso.inv_hom_id_app_assoc]

/-- An exact functor carries chain maps which become invertible in the derived category to chain
maps which do. -/
theorem isIso_Q_map_mapHomologicalComplex_map {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [IsIso (DerivedCategory.Q.map φ)] :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) := by
  have h : DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) =
      F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map φ) ≫
        F.mapDerivedCategoryFactors.hom.app L := by
    rw [F.mapDerivedCategoryFactors_hom_naturality φ, Iso.inv_hom_id_app_assoc]
  rw [h]
  infer_instance

/-- `mapExtOne` commutes with precomposition by the inverse of a chain map which becomes
invertible in the derived category. -/
theorem mapExtOne_inv_Q_map_comp {K L : CochainComplex C ℤ} {M : C} (φ : K ⟶ L)
    [IsIso (DerivedCategory.Q.map φ)]
    (z : DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor C 0).obj M)⟦(1 : ℤ)⟧) :
    haveI := F.isIso_Q_map_mapHomologicalComplex_map φ
    F.mapExtOne (CategoryTheory.inv (DerivedCategory.Q.map φ) ≫ z) =
      CategoryTheory.inv
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) ≫
        F.mapExtOne z := by
  have := F.isIso_Q_map_mapHomologicalComplex_map φ
  rw [IsIso.eq_inv_comp, ← mapExtOne_Q_map_comp, IsIso.hom_inv_id_assoc]

/-- `mapExtOne` commutes with negation. -/
theorem mapExtOne_neg {K : CochainComplex C ℤ} {M : C}
    (z : DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor C 0).obj M)⟦(1 : ℤ)⟧) :
    F.mapExtOne (-z) = -F.mapExtOne z := by
  simp only [mapExtOne, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

end CategoryTheory.Functor
