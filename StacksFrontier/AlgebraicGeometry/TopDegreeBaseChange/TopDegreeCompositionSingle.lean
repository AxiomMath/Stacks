module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeBaseChangeLocalPasting

/-!
# The derived-to-ordinary comparison and composition, in every degree

`derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle`
states that the comparison `Lf^*(M[0]) ⟶ (f^*M)[0]` is compatible with the composition
isomorphisms of [Stacks, Tag 0D5S], for a module placed in degree `0`. The top-degree comparison
of [Stacks, Tag 0EX3] meets it with the module placed in degree `d`, so this file proves the
same compatibility in every degree. The proof is the degree-`0` proof with the degree left free;
the homotopy-category lemmas it rests on are restated in degree `n` for the same reason.

## Main results

* `derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle_of_degree`.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open DerivedCategory

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

section Homotopy

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]

/-- `Functor.mapHomotopyCategorySingleFunctor` in degree `n` is the class of
`HomologicalComplex.singleMapHomologicalComplex`. -/
theorem mapHomotopyCategorySingleFunctor_hom_app_of_degree (T : C₁ ⥤ C₂) [T.Additive] (n : ℤ)
    (M : C₁) :
    (T.mapHomotopyCategorySingleFunctor n).hom.app M =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) := by
  have h1 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₁ n).hom.app M = 𝟙 _ := rfl
  have h2 : (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((CochainComplex.singleFunctor C₁ n).obj M) = 𝟙 _ := rfl
  have h3 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₂ n).inv.app (T.obj M)
      = 𝟙 _ := rfl
  dsimp only [Functor.mapHomotopyCategorySingleFunctor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Iso.symm_hom, h1, h2, h3]
  change (T.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) ≫
        𝟙 _ ≫ 𝟙 _ = _
  refine Eq.trans (congrArg (fun g => g ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
    (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) ≫
      𝟙 _ ≫ 𝟙 _)
    ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _)) ?_
  simp only [Category.comp_id, Category.id_comp]

variable {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} [F.Additive] [G.Additive] [H.Additive]

/-- `mapHomologicalComplexCompIso_hom_app_single_comp` in an arbitrary degree. -/
theorem mapHomologicalComplexCompIso_hom_app_single_comp_of_degree (e : F ⋙ G ≅ H) (n : ℤ)
    (M : C₁) :
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor C₁ n).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) n).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (ComplexShape.up ℤ) n).hom.app M ≫
      (CochainComplex.singleFunctor C₃ n).map (e.hom.app M) := by
  ext i
  by_cases h : i = n
  · subst h
    have h0 : ((CochainComplex.singleFunctor C₃ i).map (e.hom.app M)).f i =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (G.obj (F.obj M))).hom ≫
          e.hom.app M ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (H.obj M)).inv :=
      HomologicalComplex.single_map_f_self _ i _
    simp only [Functor.mapHomologicalComplexCompIso] at *
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Functor.comp_map, h0,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_right_assoc]
    exact (e.hom.naturality _).symm
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ h]

/-- `mapHomotopyCategoryCompIso_hom_app_single_comp` in an arbitrary degree. -/
theorem mapHomotopyCategoryCompIso_hom_app_single_comp_of_degree (e : F ⋙ G ≅ H) (n : ℤ)
    (M : C₁) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor C₁ n).obj M) ≫
      (H.mapHomotopyCategorySingleFunctor n).hom.app M =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategorySingleFunctor n).hom.app M) ≫
      (G.mapHomotopyCategorySingleFunctor n).hom.app (F.obj M) ≫
      (HomotopyCategory.singleFunctor C₃ n).map (e.hom.app M) := by
  have hcomp : (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategorySingleFunctor n).hom.app M) ≫
      (G.mapHomotopyCategorySingleFunctor n).hom.app (F.obj M) =
      ((F ⋙ G).mapHomotopyCategorySingleFunctor n).hom.app M := by
    rw [mapHomotopyCategorySingleFunctor_hom_app_of_degree F n M,
      mapHomotopyCategorySingleFunctor_hom_app_of_degree G n (F.obj M),
      mapHomotopyCategorySingleFunctor_hom_app_of_degree (F ⋙ G) n M]
    exact ((HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (fun t => (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map t)
        (HomologicalComplex.singleMapHomologicalComplex_hom_app_comp (ComplexShape.up ℤ) F G n M))
  rw [reassoc_of% hcomp, mapHomotopyCategorySingleFunctor_hom_app_of_degree (F ⋙ G) n M,
    mapHomotopyCategorySingleFunctor_hom_app_of_degree H n M]
  have hq := Functor.mapHomotopyCategoryCompIso_hom_app_quotient e
    ((CochainComplex.singleFunctor C₁ n).obj M)
  have hs : (HomotopyCategory.singleFunctor C₃ n).map (e.hom.app M) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor C₃ n).map (e.hom.app M)) := rfl
  refine (congrArg (· ≫ _) hq).trans ?_
  rw [hs]
  exact ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (mapHomologicalComplexCompIso_hom_app_single_comp_of_degree e n M))).trans
    (Functor.map_comp _ _ _)

end Homotopy

section DerivedToOrdinary

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

variable {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The comparison from derived to ordinary pullback is compatible with composition, in every
degree.** This is
`derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle` with the degree
`0` replaced by an arbitrary `d`; the proof is the same. -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle_of_degree
    (M : SheafOfModules.{u} (structureSheafRing Z)) (d : ℤ) :
    (derivedPullbackCompIsoCanonical a b).hom.app
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M) ≫
      derivedToOrdinaryPullbackSingle (a ≫ b) M d =
    (derivedPullback a).map (derivedToOrdinaryPullbackSingle b M d) ≫
      derivedToOrdinaryPullbackSingle a ((modulePullback b).obj M) d ≫
      (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M) := by
  have hcoh :=
    Cohomology.DerivedPushforwardComposition.derivedPullbackCompIsoCanonical_hom_app_comp_comparison
      a b ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)
  have hnatI := (derivedPullbackCompIsoCanonical a b).hom.naturality
    ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Z)) d).hom.app M)
  have hnatC := (derivedPullbackComparison a).naturality
    ((Functor.mapHomotopyCategorySingleFunctor (modulePullback b) d).hom.app M)
  have hkey : Qh.map ((pullbackOnHomotopyCompIso a b).hom.app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)) ≫
      Qh.map (((modulePullback (a ≫ b)).mapHomotopyCategorySingleFunctor d).hom.app M) =
    Qh.map (((modulePullback a).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePullback b).mapHomotopyCategorySingleFunctor d).hom.app M)) ≫
      Qh.map (((modulePullback a).mapHomotopyCategorySingleFunctor d).hom.app
        ((modulePullback b).obj M)) ≫
      Qh.map ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg Qh.map (mapHomotopyCategoryCompIso_hom_app_single_comp_of_degree
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b) d M)
  have hnatS :=
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.naturality
      ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M)
  have hc : (derivedPullback a).map
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).inv.app
          ((modulePullback b).obj M)) ≫
      (derivedPullback a).map
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app
          ((modulePullback b).obj M)) = 𝟙 _ :=
    ((derivedPullback a).mapIso
      (((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).app
        ((modulePullback b).obj M)).symm)).hom_inv_id
  unfold derivedToOrdinaryPullbackSingle
  simp only [Functor.map_comp, Category.assoc]
  exact comp_eq_of_six _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnatI hcoh hc hnatC hkey hnatS

end DerivedToOrdinary


end Stacks.AlgebraicGeometry.TopDegreeBaseChange
