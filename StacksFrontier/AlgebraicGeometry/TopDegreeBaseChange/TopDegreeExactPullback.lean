module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ExactFunctorSingleHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionComp

/-!
# The top-degree comparison along a morphism with exact pullback
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open _root_.DerivedCategory

universe u

section Chain

variable {𝒞 : Type*} [Category 𝒞]

/-- The rearrangement behind `mapDerivedCategorySingleFunctor_hom_app_eq_factorsh`, at
variables. -/
theorem transverse_single_chain {P₀ P₁ P₂ P₃ P₄ P₅ : 𝒞}
    (sh : P₀ ⟶ P₁) (qi : P₀ ⟶ P₁) (fh : P₁ ⟶ P₃) (qh : P₁ ⟶ P₀) (fac : P₀ ⟶ P₂) (qa : P₂ ⟶ P₃)
    (idm : P₃ ⟶ P₃) (hs : P₃ ⟶ P₄) (qsm : P₃ ⟶ P₄) (sm : P₂ ⟶ P₅) (qa' : P₅ ⟶ P₄)
    (sa : P₄ ⟶ P₅) (m : P₀ ⟶ P₅)
    (e₁ : sh = qi) (e₂ : fh = qh ≫ fac ≫ qa ≫ idm) (e₃ : idm = 𝟙 _) (e₄ : hs = qsm)
    (e₅ : sm ≫ qa' = qa ≫ qsm)
    (e₆ : qa' ≫ sa = 𝟙 _) (e₇ : m = fac ≫ sm) (e₈ : qi ≫ qh = 𝟙 _) :
    sh ≫ fh ≫ hs ≫ sa = m := by
  rw [e₁, e₂, e₃, e₄, e₇]
  simp only [assoc, id_comp]
  rw [← assoc qi, e₈, id_comp, ← assoc qa, ← e₅, assoc, e₆, comp_id]

/-- The rearrangement behind `derivedPullbackIsoMapDerivedCategory_hom_app_single`. -/
theorem transverse_exact_chain {P₀ P₁ P₂ P₃ P₄ P₅ P₇ : 𝒞}
    (iso₁ : P₀ ⟶ P₁) (mD : P₁ ⟶ P₇) (dT : P₀ ⟶ P₇) (lfs : P₀ ⟶ P₂) (isoQ : P₂ ⟶ P₃)
    (Ds : P₁ ⟶ P₃) (fh : P₃ ⟶ P₄) (qm : P₄ ⟶ P₅) (sai : P₅ ⟶ P₇) (cmp : P₂ ⟶ P₄)
    (hn : lfs ≫ isoQ = iso₁ ≫ Ds) (hsc : Ds ≫ fh ≫ qm ≫ sai = mD) (hl : isoQ ≫ fh = cmp)
    (hd : dT = lfs ≫ cmp ≫ qm ≫ sai) : iso₁ ≫ mD = dT := by
  rw [← hsc, hd, ← hl, ← assoc iso₁, ← hn]
  simp only [assoc]

/-- The rearrangement behind `derivedPullbackTopDegreeIsoPullback_hom_eq_of_exact`. -/
theorem transverse_exact_top_chain {P₀ P₁ P₂ P₃ P₄ P₅ : 𝒞}
    (θ : P₀ ⟶ P₅) (a : P₀ ⟶ P₁) (sm : P₁ ⟶ P₅) (b : P₁ ⟶ P₂) (m₁ : P₂ ⟶ P₃) (χf : P₃ ⟶ P₅)
    (c : P₀ ⟶ P₄) (d : P₄ ⟶ P₂) (mK : P₄ ⟶ P₅) (fk : P₅ ⟶ P₃)
    (t₀ : θ = a ≫ sm) (hs : sm = b ≫ m₁ ≫ χf) (n₁ : a ≫ b = c ≫ d)
    (n₂ : d ≫ m₁ = mK ≫ fk) (e₁ : fk ≫ χf = 𝟙 _) : θ = c ≫ mK := by
  rw [t₀, hs, ← assoc, n₁, assoc, ← assoc d, n₂, assoc, e₁, comp_id]

end Chain

section Exact

variable {C A : Type*} [Category C] [Category A] [Abelian C] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory A]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The components of `Functor.mapDerivedCategorySingleFunctor`, in every degree. -/
theorem mapDerivedCategorySingleFunctor_hom_app_of_degree (n : ℤ) (X : C) :
    (F.mapDerivedCategorySingleFunctor n).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C n).obj X) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X) := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor, singleFunctorIsoCompQ,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Q_obj_single_obj, Functor.whiskerRight_app, NatTrans.id_app,
    comp_id, id_comp]
  exact id_comp _

/-- **The single-functor comparison of `F.mapDerivedCategory` read through the homotopy category**,
in every degree. -/
theorem mapDerivedCategorySingleFunctor_hom_app_eq_factorsh (n : ℤ) (X : C) :
    F.mapDerivedCategory.map ((singleFunctorIsoCompQh C n).hom.app X) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C n).obj X) ≫
        Qh.map ((F.mapHomotopyCategorySingleFunctor n).hom.app X) ≫
        (singleFunctorIsoCompQh A n).inv.app (F.obj X) =
      (F.mapDerivedCategorySingleFunctor n).hom.app X := by
  have e₁ := congrArg F.mapDerivedCategory.map
    (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := C) n X)
  have e₂ := F.mapDerivedCategoryFactorsh_hom_app ((CochainComplex.singleFunctor C n).obj X)
  have e₃ : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((CochainComplex.singleFunctor C n).obj X) = 𝟙 _ := rfl
  have e₄ := mapHomotopyCategorySingleFunctor_hom_app_of_degree F n X
  have e₅ := (quotientCompQhIso A).inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X)
  have e₆ : (quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A n).obj (F.obj X)) ≫
      (singleFunctorIsoCompQh A n).inv.app (F.obj X) = 𝟙 _ := by
    rw [← Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := A) n (F.obj X)]
    exact Iso.hom_inv_id_app _ _
  have e₇ := mapDerivedCategorySingleFunctor_hom_app_of_degree F n X
  have e₈ := (F.mapDerivedCategory.mapIso ((quotientCompQhIso C).app
    ((CochainComplex.singleFunctor C n).obj X))).inv_hom_id
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at e₈
  simp only [Functor.comp_map] at e₅
  exact transverse_single_chain _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂
    ((congrArg Qh.map e₃).trans (Qh.map_id _)) (congrArg Qh.map e₄) e₅ e₆ e₇ e₈

end Exact

section Geometry

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]

/-- **For a morphism with exact pullback, `Lf^* ≅ D(f^*)` at a single complex is the comparison
from derived to ordinary pullback**, in every degree. -/
theorem derivedPullbackIsoMapDerivedCategory_hom_app_single
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app
        ((singleFunctor _ d).obj M) ≫
      ((modulePullback f).mapDerivedCategorySingleFunctor d).hom.app M =
    derivedToOrdinaryPullbackSingle f M d := by
  have hn := NatTrans.naturality
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom
    ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app M)
  have hsc := mapDerivedCategorySingleFunctor_hom_app_eq_factorsh (modulePullback f) d M
  have hl := Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app (modulePullback f)
    (derivedPullback f) (derivedPullbackComparison f)
    ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)
  exact transverse_exact_chain _ _ _ _ _ _ _ _ _ _ hn hsc hl rfl

/-- **For a morphism with exact pullback, the comparison `H^d(Lf^*(M[-d])) ⟶ f^*M` is the
identification `Lf^* ≅ D(f^*)` followed by the commutation of `D(f^*)` with `H^d`.** -/
theorem homologyDerivedPullbackSingleMap_eq_of_exact
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    homologyDerivedPullbackSingleMap f M d =
      (homologyFunctor _ d).map
          ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app
            ((singleFunctor _ d).obj M)) ≫
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
            (modulePullback f) d).hom.app
          ((singleFunctor _ d).obj M) ≫
        (modulePullback f).map
          ((singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Y))
            d).hom.app M) := by
  have h1 := Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor
    (modulePullback f) d M
  rw [(modulePullback f).mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso,
    ← Stacks.Gysin.mapDerivedCategoryHomologyIso_eq] at h1
  rw [homologyDerivedPullbackSingleMap, homologySingleIso_hom,
    ← derivedPullbackIsoMapDerivedCategory_hom_app_single f M d, Functor.map_comp, assoc, h1]

/-- **For a morphism with exact pullback, the top-degree comparison is the identification
`Lf^* ≅ D(f^*)` followed by the commutation of `D(f^*)` with `H^d`.** -/
theorem derivedPullbackTopDegreeIsoPullback_hom_eq_of_exact
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (derivedPullbackTopDegreeIsoPullback f K d hK).hom =
      (homologyFunctor _ d).map
          ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app
            K) ≫
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
            (modulePullback f) d).hom.app K := by
  have e0 : (homologyFunctor _ d).map (topDegreeSingleMap K d hK) ≫
      (singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app
        ((homologyFunctor _ d).obj K) = 𝟙 _ := by
    rw [homologyMap_topDegreeSingleMap, Iso.inv_hom_id_app]
    rfl
  have e₁ := ((modulePullback f).map_comp _ _).symm.trans
    ((congrArg (modulePullback f).map e0).trans ((modulePullback f).map_id _))
  have n₁ := congrArg (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.naturality
      (topDegreeSingleMap K d hK))
  simp only [Functor.map_comp] at n₁
  have n₂ := (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (modulePullback f)
    d).hom.naturality (topDegreeSingleMap K d hK)
  simp only [Functor.comp_map] at n₂
  exact transverse_exact_top_chain _ _ _ _ _ _ _ _ _ _
    (derivedPullbackTopDegreeIsoPullback_hom_eq f K d hK)
    (homologyDerivedPullbackSingleMap_eq_of_exact f _ d) n₁ n₂ e₁

end Geometry

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
