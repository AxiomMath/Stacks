module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupUnitSection
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeUnitClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObjectDegreeZero

/-!
# The bridge on the class of a global section

The bridge `Stacks.DeRham.GysinCupHodge.hgroupModuleShiftIso` from the cohomology group
`H⁰(X, G)` to the cohomology module of the derived global sections of `G[0]` carries the class
of a global section `u` of `G` to the image of the class of `1` under the chain map
`𝒪[0] ⟶ G[0]` of `u` (`hgroupModuleShiftIso_sectionClass`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRham.CohomologicalGysin
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (baseRingedSpace)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

/-- A functor applied to a composite of six morphisms, the last split off. At variables. -/
private lemma map_comp_last {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : D} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄)
    (e : P₄ ⟶ P₅) (f : P₅ ⟶ P₆) :
    H.map (a ≫ b ≫ c ≫ d ≫ e ≫ f) = H.map (a ≫ b ≫ c ≫ d ≫ e) ≫ H.map f := by
  simp

/-- The algebra of `toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv`, at variables. -/
private lemma bridgeZero_chase {V : Type*} [Category* V] {P Q₁ Q₂ D₁ D₂ D₃ D₄ E₂ C H₀ H₁ : V}
    (td : P ⟶ Q₁) (ci : Q₁ ⟶ Q₂) (hfi : Q₂ ⟶ E₂) (zc : P ⟶ D₁) (qc : D₁ ⟶ D₂) (Hα : D₂ ⟶ D₃)
    (Hrφ : D₃ ⟶ Q₂) (l : P ⟶ C) (π : C ⟶ H₀) (HFi : H₀ ⟶ D₁) (hcfi : H₀ ⟶ H₁) (hffi : H₁ ⟶ D₂)
    (hfi' : D₃ ⟶ D₄) (ΦHφ : D₄ ⟶ E₂) (Φp : P ⟶ D₄) (ΦL : P ⟶ E₂)
    (hgen : td ≫ ci = zc ≫ qc ≫ Hα ≫ Hrφ) (hzc : zc = l ≫ π ≫ HFi)
    (h4 : HFi ≫ qc = hcfi ≫ hffi) (h3 : Hrφ ≫ hfi = hfi' ≫ ΦHφ)
    (h5 : l ≫ π ≫ hcfi ≫ hffi ≫ Hα ≫ hfi' = Φp) (hL : ΦL = Φp ≫ ΦHφ) :
    td ≫ ci ≫ hfi = ΦL := by
  rw [hL, ← h5, ← Category.assoc td, hgen, hzc]
  simp only [Category.assoc]
  rw [reassoc_of% h4, h3]

/-- The inverse of an isomorphism whose morphism is the inverse of another. At variables. -/
private lemma inv_eq_hom_of_hom_eq_inv {V : Type*} [Category* V] {P Q : V} (a : P ≅ Q)
    (b : Q ≅ P) (h : a.hom = b.inv) : a.inv = b.hom := by
  rw [← cancel_epi a.hom, Iso.hom_inv_id, h, Iso.inv_hom_id]

/-- A functor applied to a composite of three morphisms. At variables. -/
private lemma map_comp_three {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P₀ P₁ P₂ P₃ : D} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) :
    H.map a ≫ H.map b ≫ H.map c = H.map (a ≫ b ≫ c) := by
  simp

/-- The algebra of `unitClass_sectionsUnitQ`, at variables. -/
private lemma moduleZero_chase {V : Type*} [Category* V] {P C C' H₀ H₁ D₁ D₂ D₃ D₄ H₀' D₁' D₄' : V}
    (l : P ⟶ C) (π : C ⟶ H₀) (hcfi : H₀ ⟶ H₁) (hffi : H₁ ⟶ D₂) (Hu : D₂ ⟶ D₃) (Hφ : D₃ ⟶ D₄)
    (He : D₄ ⟶ D₄') (HFi : H₀ ⟶ D₁) (Hq : D₁ ⟶ D₂) (Hs : D₁ ⟶ D₄) (Hcx : H₀ ⟶ H₀')
    (HFi' : H₀' ⟶ D₁') (Hs' : D₁' ⟶ D₄') (cm : C ⟶ C') (π' : C' ⟶ H₀') (HQ : D₁ ⟶ D₁')
    (h1 : hcfi ≫ hffi = HFi ≫ Hq) (h2 : Hq ≫ Hu ≫ Hφ = Hs) (h3 : HQ ≫ Hs' = Hs ≫ He)
    (h4 : HFi ≫ HQ = Hcx ≫ HFi') (h5 : π ≫ Hcx = cm ≫ π') :
    l ≫ π ≫ hcfi ≫ hffi ≫ Hu ≫ Hφ ≫ He = (l ≫ cm) ≫ π' ≫ HFi' ≫ Hs' := by
  rw [reassoc_of% h1, reassoc_of% h2, ← h3, reassoc_of% h4, reassoc_of% h5]
  simp only [Category.assoc]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

variable (X : RingedSpace.{u, u})

/-- **The abelian half of the bridge on degree-zero classes**: `toRightDerivedZero`, followed by
the inverse of `cohomologyDerivedSingleIso` and by `homologyForgetIso`, is the forgetful functor
applied to the class of the degree-`0` cocycles of the global sections of `G[0]`, carried by the
unit of the derived global sections over the base ring. -/
theorem toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv
    (G : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (secF (structureSheafRing X) (⊤ : TopologicalSpace.Opens X.carrier)).toRightDerivedZero.app G ≫
        (cohomologyDerivedSingleIso X G ((0 : ℕ) : ℤ) 0 0 (by simp)).inv ≫
        (homologyForgetIso X 0 ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj G)).hom =
      (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
        ((((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G)).liftCycles
            ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv) 1 (by simp)
            (Stacks.DerivedFunctor.singleZeroClass_d _ G) ≫
          HomologicalComplex.homologyπ _ 0 ≫
          (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) 0).inv.app _ ≫
          (DerivedCategory.homologyFunctorFactorsh _ 0).inv.app _ ≫
          (DerivedCategory.homologyFunctor _ 0).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                ((CochainComplex.singleFunctor _ 0).obj G))) ≫
          (DerivedCategory.homologyFunctor _ 0).map ((baseSections X).map
            ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app G))) := by
  let := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  have h₀ := cohomologyDerivedSingleIso_hom_eq X G ((0 : ℕ) : ℤ) 0 0 (by simp)
  have hz := homology_single_shift_zero (derivedGlobalSections X) G (-((0 : ℕ) : ℤ)) 0
    (by simp) (by simp) (by simp)
  have h₀' := h₀.trans ((congrArg (· ≫ _) hz).trans (Category.id_comp _))
  have hinv := congrArg Iso.inv (Iso.ext h₀')
  have hgen := Stacks.DerivedFunctor.toRightDerivedZero_comp_homologyTotalRightDerivedSingleIso_inv
    (secF (structureSheafRing X) (⊤ : TopologicalSpace.Opens X.carrier)) (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X)
    (Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves X) G
  rw [← hinv] at hgen
  have h3 := homologyForgetIso_hom_naturality X 0
    ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app G)
  have h4 := Stacks.DerivedFunctor.homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv
    AddCommGrpCat.{u} (((secF (structureSheafRing X)
      (⊤ : TopologicalSpace.Opens X.carrier)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj G)) 0
  have h5 := homologyForgetIso_unitClass X ((CochainComplex.singleFunctor _ 0).obj G)
    ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv)
    (Stacks.DerivedFunctor.singleZeroClass_d _ G)
  exact bridgeZero_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgen rfl h4 h3 h5
    (map_comp_last _ _ _ _ _ _ _)

/-- **The module half of the bridge on degree-zero classes**: the class of the cocycles of
`Γ(G[0])` carried by the unit, read through the extension of `G[0]` by zero, is the class of the
corresponding global cocycles of the extension. -/
theorem unitClass_sectionsUnitQ (G : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G)).liftCycles
            ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv) 1 (by simp)
            (Stacks.DerivedFunctor.singleZeroClass_d _ G) ≫
          HomologicalComplex.homologyπ _ 0 ≫
          (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) 0).inv.app _ ≫
          (DerivedCategory.homologyFunctorFactorsh _ 0).inv.app _ ≫
          (DerivedCategory.homologyFunctor _ 0).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                ((CochainComplex.singleFunctor _ 0).obj G))) ≫
          (DerivedCategory.homologyFunctor _ 0).map ((baseSections X).map
            ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app G)) ≫
          (DerivedCategory.homologyFunctor _ 0).map ((baseSections X).map
            (DerivedCategory.Q.map (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              G 0 0 rfl).inv)) =
      ((((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G)).liftCycles
            ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv) 1 (by simp)
            (Stacks.DerivedFunctor.singleZeroClass_d _ G) ≫
          HomologicalComplex.cyclesMap (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X
            ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv) 0) ≫
        HomologicalComplex.homologyπ _ 0 ≫
        (DerivedCategory.homologyFunctorFactors _ 0).inv.app _ ≫
        (DerivedCategory.homologyFunctor _ 0).map
          (Stacks.Cohomology.DerivedSectionsLeray.sectionsUnitQ X ⊤
            ((singleNat (X := X) G 0).extend ComplexShape.embeddingUpNat)) := by
  let M := ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G)
  let φ := ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv
  have h1 := (Stacks.DerivedFunctor.homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv
    _ M 0).symm
  have h2 : (DerivedCategory.homologyFunctor _ 0).map
        ((DerivedCategory.quotientCompQhIso _).inv.app M) ≫
      (DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj G))) ≫
      (DerivedCategory.homologyFunctor _ 0).map ((baseSections X).map
        ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app G)) =
      (DerivedCategory.homologyFunctor _ 0).map
        (Stacks.Cohomology.DerivedSectionsLeray.sectionsUnitQ X ⊤
          ((CochainComplex.singleFunctor _ 0).obj G)) := by
    have e := Stacks.DerivedFunctor.singleFunctorIsoCompQh_hom_app G
    have hinv := inv_eq_hom_of_hom_eq_inv ((DerivedCategory.singleFunctorIsoCompQh _ 0).app G)
      ((DerivedCategory.quotientCompQhIso _).app ((CochainComplex.singleFunctor _ 0).obj G)) e
    exact (map_comp_three _ _ _ _).trans (congrArg (fun t =>
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
        ((DerivedCategory.quotientCompQhIso _).inv.app M ≫
          (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X ⊤).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor _ 0).obj G)) ≫ (baseSections X).map t)) hinv)
  have h3 := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).map
    (Stacks.Cohomology.DerivedSectionsLeray.sectionsUnitQ_naturality X ⊤
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv)
  rw [Functor.map_comp, Functor.map_comp] at h3
  have h4 :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing X)) 0).inv.naturality φ
  have h5 := HomologicalComplex.homologyπ_naturality φ 0
  exact moduleZero_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4.symm h5

/-- Two composites with a common last factor, on elements whose images agree. At variables. -/
private lemma comp_apply_eq_of_eq {R : Type u} [Ring R] {A B C D : ModuleCat.{u} R} (f₁ : A ⟶ B)
    (f₂ : C ⟶ B) (T : B ⟶ D) (x : A) (y : C) (h : f₁.hom x = f₂.hom y) :
    (f₁ ≫ T).hom x = (f₂ ≫ T).hom y := by
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h]

open Stacks.Cohomology.DerivedGlobalCupProduct (globalCycleClass unitCycleHom) in
/-- **The cocycle of a global section.** The cocycle `u` of the global sections of `G[0]`, read
on the extension by zero, is the image of the cocycle `1` of the unit complex under the chain
map of `u`. -/
theorem unitComplexSectionMap_cycle
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (u : G.val.sections) :
    ((((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G)).liftCycles
            ((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv) 1 (by simp)
            (Stacks.DerivedFunctor.singleZeroClass_d _ G) ≫
          HomologicalComplex.cyclesMap (((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X
            ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv) 0).hom
        (u.eval (Opposite.op ⊤)) =
      (unitCycleHom (baseRingedSpace X.sheaf) ≫
        HomologicalComplex.cyclesMap
          (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
            (baseRingedSpace X.sheaf)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (unitComplexSectionMap G u)) 0).hom 1 := by
  have hi : Function.Injective ((((Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X
      ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((singleNat (X := X) G 0).extend ComplexShape.embeddingUpNat)).iCycles 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hi
  let Γm := Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X ⊤
  have eL := HomologicalComplex.liftCycles_i
    ((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj G))
    (Γm.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv) 1 (by simp)
    (Stacks.DerivedFunctor.singleZeroClass_d _ G)
  have eL' := HomologicalComplex.cyclesMap_i ((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv) 0
  have eR := HomologicalComplex.cyclesMap_i ((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (unitComplexSectionMap G u)) 0
  have h1 := Stacks.Cohomology.DerivedGlobalCupProduct.singleObjXSelf_hom_unitSection
    (X := baseRingedSpace X.sheaf) 0
  have h2 : ((G.unitHomEquiv.symm u).val.app (Opposite.op ⊤)).hom
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj (Opposite.op ⊤)) =
      u.eval (Opposite.op ⊤) := by
    have := _root_.SheafOfModules.unitHomEquiv_apply_coe G (G.unitHomEquiv.symm u) (Opposite.op ⊤)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h3 := Stacks.Cohomology.DerivedGlobalCupProduct.iCycles_unitCycle
    (X := baseRingedSpace X.sheaf) 0
  have h4 : (unitCycleHom (baseRingedSpace X.sheaf)).hom 1 =
      Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (X := baseRingedSpace X.sheaf) 0 :=
    one_smul _ _
  have L := (ConcreteCategory.congr_hom eL' _).trans (congrArg (ConcreteCategory.hom
    (((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv).f 0))
    (ConcreteCategory.congr_hom eL (u.eval (Opposite.op ⊤))))
  have R := (ConcreteCategory.congr_hom eR
    ((unitCycleHom (baseRingedSpace X.sheaf)).hom 1)).trans (congrArg (ConcreteCategory.hom
      (((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map (unitComplexSectionMap G u)).f 0))
      ((congrArg _ h4).trans h3))
  refine L.trans (Eq.trans ?_ R.symm)
  have hu : ((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map (unitComplexSectionMap G u)).f 0 =
      Γm.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (_root_.SheafOfModules.unit _)).hom ≫
        Γm.map (G.unitHomEquiv.symm u) ≫
        Γm.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫
        ((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv).f 0 := by
    simp only [unitComplexSectionMap, Functor.map_comp, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.single_map_f_self, Category.assoc]
    rfl
  rw [hu]
  simp only [ConcreteCategory.comp_apply]
  exact congrArg (fun t => (ConcreteCategory.hom
      (((Γm.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv).f 0))
      ((ConcreteCategory.hom
        (Γm.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv))
        t)) ((congrArg (fun t => ((G.unitHomEquiv.symm u).val.app (Opposite.op ⊤)).hom t) h1).trans
          h2).symm

open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyMap globalCycleClass unitCycleHom) in
/-- **(U1) The bridge carries the class of a global section to the image of the class of `1`.** -/
theorem hgroupModuleShiftIso_sectionClass
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (u : G.val.sections) :
    (hgroupModuleShiftIso G 0 0 0 (by simp)).hom (sectionClass u) =
      (cohomologyMap (S := baseRingedSpace X.sheaf) (unitComplexSectionMap G u) 0).hom
        ((globalCycleClass (S := baseRingedSpace X.sheaf)
          (unitCycleHom (baseRingedSpace X.sheaf))).hom 1) := by
  have hA := toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv X G
  have hM := unitClass_sectionsUnitQ X G
  have e1 := ConcreteCategory.congr_hom (congrArg (· ≫ (forget₂ (ModuleCat.{u} (baseRing X))
    AddCommGrpCat.{u}).map ((DerivedCategory.homologyFunctor _ 0).map ((baseSections X).map
      (DerivedCategory.Q.map (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        G 0 0 rfl).inv)))) hA) (u.eval (Opposite.op ⊤))
  have e2 := ConcreteCategory.congr_hom hM (u.eval (Opposite.op ⊤))
  have e3 := ConcreteCategory.congr_hom
    (Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_map
    (S := baseRingedSpace X.sheaf) (unitCycleHom (baseRingedSpace X.sheaf))
    (unitComplexSectionMap G u)) (1 : baseRing X)
  refine e1.trans (e2.trans (Eq.trans ?_ e3.symm))
  exact comp_apply_eq_of_eq _ _ _ _ _ (unitComplexSectionMap_cycle X G u)

end StandardModel

end Stacks.DeRham.GysinCupHodge
