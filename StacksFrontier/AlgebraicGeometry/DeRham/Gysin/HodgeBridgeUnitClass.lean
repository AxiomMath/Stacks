module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomology

/-!
# The bridge from cohomology groups to cohomology modules on classes of cocycles

The comparison `Stacks.DeRham.GysinCupHodge.homologyForgetIso` of the derived global sections in
abelian groups with the derived global sections over the base ring carries the class, through the
unit of the first, of a cocycle of global sections to the class, through the unit of the second, of
the same cocycle (`homologyForgetIso_unitClass`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRham.CohomologicalGysin
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)

universe u

namespace Stacks.DeRham.GysinCupHodge

section Generic

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  (Φ : C₁ ⥤ C₂) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

omit [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
/-- The image of a degree-`0` cocycle under an additive functor is a cocycle. -/
lemma map_cocycle_d (M : CochainComplex C₁ ℤ) {Y : C₁} (z : Y ⟶ M.X 0)
    (hz : z ≫ M.d 0 1 = 0) :
    Φ.map z ≫ ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).d 0 1 = 0 := by
  rw [Functor.mapHomologicalComplex_obj_d, ← Φ.map_comp, hz, Φ.map_zero]

/-- An exact functor carries the class of a degree-`0` cocycle to the class of its image. -/
theorem map_liftCycles_homologyπ (M : CochainComplex C₁ ℤ) {Y : C₁} (z : Y ⟶ M.X 0)
    (hz : z ≫ M.d 0 1 = 0) :
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).liftCycles (Φ.map z) 1 (by simp)
        (map_cocycle_d Φ M z hz) ≫
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homologyπ 0 ≫
      (Stacks.DerivedIndexing.mapExactHomologyIso Φ M 0).hom =
    Φ.map (M.liftCycles z 1 (by simp) hz ≫ M.homologyπ 0) := by
  have hm := Stacks.DerivedIndexing.mono_map_iCycles Φ M (j := 0)
  have h₁ : ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).liftCycles (Φ.map z) 1
      (by simp) (map_cocycle_d Φ M z hz) ≫
      (Stacks.DerivedIndexing.mapExactCyclesIso Φ M 0).hom =
      Φ.map (M.liftCycles z 1 (by simp) hz) := by
    refine (cancel_mono (Φ.map (M.iCycles 0))).1 ?_
    rw [Category.assoc, Stacks.DerivedIndexing.mapExactCyclesIso_hom_iCycles,
      HomologicalComplex.liftCycles_i, ← Φ.map_comp, HomologicalComplex.liftCycles_i]
  rw [Stacks.DerivedIndexing.homologyπ_mapExactHomologyIso_hom, reassoc_of% h₁, Φ.map_comp]

end Generic

section Unit

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

variable (X : RingedSpace.{u, u})

/-- The components of the unit `forgetUnit`. -/
theorem forgetUnit_app (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
    (ComplexShape.up ℤ)) :
    (forgetUnit X).app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (sectionsForgetIso X)
          (ComplexShape.up ℤ)).inv.app K) ≫
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv.app
          (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapDerivedCategory.map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app K) := by
  simp [forgetUnit]

/-- The comparison of the two functors on homotopy categories induced by the identification of
global sections in abelian groups is the identity at the class of a complex. -/
theorem mapHomotopyCategoryCompIso_sectionsForgetIso_inv_app
    (N : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (sectionsForgetIso X) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) = 𝟙 _ := by
  simp only [Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift]
  refine (Quotient.natTransLift_app _ _ _ _ N).trans ?_
  dsimp only [Functor.isoWhiskerRight_inv, Functor.whiskerRight_app]
  refine (congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ?_).trans
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id _)
  ext n : 1
  rfl

/-- A functor applied to a composite of five morphisms. -/
private lemma map_comp_five {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P₀ P₁ P₂ P₃ P₄ P₅ : D} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄)
    (e : P₄ ⟶ P₅) : H.map (a ≫ b ≫ c ≫ d ≫ e) = H.map (a ≫ b) ≫ H.map c ≫ H.map d ≫ H.map e := by
  simp

/-- A functor applied to a factorisation whose first factor is an identity. -/
private lemma map_comp_of_eq {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E) {P Q R S : D}
    {a : P ⟶ Q} {b : Q ⟶ R} {e : P ⟶ P} {c : P ⟶ S} {d : S ⟶ R} (h : a ≫ b = e ≫ c ≫ d)
    (he : e = 𝟙 P) : H.map a ≫ H.map b = H.map c ≫ H.map d := by
  rw [← H.map_comp, h, he, Category.id_comp, H.map_comp]

/-- An identity of composites in a category, from the listed relations between their factors. -/
private lemma unitClass_chase {V : Type*} [Category* V] {P C H₀ H₁ D₁ D₂ D₃ D₄ E E' W₁ W₂ : V}
    (l' : P ⟶ C) (π' : C ⟶ H₀) (hcfi : H₀ ⟶ H₁) (hffi : H₁ ⟶ D₁) (Hα : D₁ ⟶ D₂) (Hν : D₂ ⟶ D₃)
    (md : D₃ ⟶ E) (Hfi : D₁ ⟶ D₄) (Hu : D₄ ⟶ D₃) (md' : D₄ ⟶ E') (ΦHu : E' ⟶ E)
    (HFh : D₄ ⟶ D₁) (hffh : D₁ ⟶ H₁) (hcf : H₁ ⟶ H₀) (mEHI : H₀ ⟶ W₁) (Φhcfi : W₁ ⟶ W₂)
    (Φhffi : W₂ ⟶ E') (ΦLπ : P ⟶ W₁) (ΦR : P ⟶ E)
    (hαν : Hα ≫ Hν = Hfi ≫ Hu) (hnat : Hu ≫ md = md' ≫ ΦHu)
    (hmd' : md' = HFh ≫ hffh ≫ (hcf ≫ mEHI ≫ Φhcfi) ≫ Φhffi) (hFh : Hfi ≫ HFh = 𝟙 D₁)
    (hi1 : hffi ≫ hffh = 𝟙 H₁) (hi2 : hcfi ≫ hcf = 𝟙 H₀) (hg : l' ≫ π' ≫ mEHI = ΦLπ)
    (hR : ΦR = ΦLπ ≫ Φhcfi ≫ Φhffi ≫ ΦHu) :
    l' ≫ π' ≫ hcfi ≫ hffi ≫ Hα ≫ Hν ≫ md = ΦR := by
  rw [hR, reassoc_of% hαν, hnat, hmd']
  simp only [Category.assoc]
  rw [reassoc_of% hFh, reassoc_of% hi1, reassoc_of% hi2, ← reassoc_of% hg]

/-- **The comparison of the two derived global sections on classes of global cocycles**: for a
degree-`0` cocycle `z` of the global sections of a complex `N` of `𝒪_X`-modules, the class of `z`
read in abelian groups, carried to the derived global sections in abelian groups by their unit, is
carried by `homologyForgetIso` to the class of `z` carried by the unit of the derived global
sections over the base ring. -/
theorem homologyForgetIso_unitClass
    (N : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    {Y : ModuleCat.{u} (baseRing X)}
    (z : Y ⟶ (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N).X 0)
    (hz : z ≫ (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N).d 0 1 = 0) :
    (((forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N)).liftCycles
        ((forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map z) 1 (by simp)
        (map_cocycle_d _ _ z hz) ≫
      HomologicalComplex.homologyπ _ 0 ≫
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).inv.app _ ≫
      (DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedGlobalSectionsUnit X).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
      (homologyForgetIso X 0 (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))).hom =
    (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
      ((((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N).liftCycles z 1 (by simp) hz ≫
        HomologicalComplex.homologyπ _ 0 ≫
        (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) 0).inv.app _ ≫
        (DerivedCategory.homologyFunctorFactorsh _ 0).inv.app _ ≫
        (DerivedCategory.homologyFunctor _ 0).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))) := by
  let Φ := forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}
  let Γm := Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤
  let M := (Γm.mapHomologicalComplex (ComplexShape.up ℤ)).obj N
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N
  let HD := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
  have hfac := (derivedGlobalSectionsForget_fac_app X K).trans (forgetUnit_app X K)
  have hαν := map_comp_of_eq HD hfac ((congrArg DerivedCategory.Qh.map
    (mapHomotopyCategoryCompIso_sectionsForgetIso_inv_app X N)).trans (DerivedCategory.Qh.map_id _))
  have hnat : HD.map (Φ.mapDerivedCategory.map
        ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app K)) ≫
        (Φ.mapDerivedCategoryHomologyIso 0).hom.app
          ((baseSections X).obj (DerivedCategory.Qh.obj K)) =
      (Φ.mapDerivedCategoryHomologyIso 0).hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
        Φ.map ((DerivedCategory.homologyFunctor _ 0).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app K)) :=
    (Φ.mapDerivedCategoryHomologyIso 0).hom.naturality
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app K)
  have hform := Φ.mapDerivedCategoryHomologyIso_hom_app_Qh_quotient 0 M
  rw [Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient] at hform
  have hg := map_liftCycles_homologyπ Φ M z hz
  exact unitClass_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hαν hnat hform
    ((HD.map_comp _ _).symm.trans ((congrArg HD.map (Iso.inv_hom_id_app _ _)).trans
      (HD.map_id _))) (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) hg
    (map_comp_five Φ _ _ _ _ _)

end Unit

end Stacks.DeRham.GysinCupHodge
