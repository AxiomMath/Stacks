module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationUnboundedGlobalClass
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge

/-!
# Čech classes of global cocycles across the realization comparison

Let `A` be a sheaf of commutative rings on a space `X` and `K` a bounded below complex of
`A`-modules. A global cocycle `s` of `Γ(X, K)` restricts to a cocycle of the total Čech complex
`Tot(Č(𝒰, K))` of an open covering (the augmentation of [Stacks, Tag 07M9]). Its class in
hypercohomology, through the comparison `Tot(Č(𝒰, K)) ⟶ RΓ(X, K)` of [Stacks, Tag 08BN], is the
class of `s` given by the unit `Γ(X, -) ⟶ RΓ(X, -)`, in either model of derived global sections;
and through the comparison of [Stacks, Tag 01F1] it is the class of `s` in the hypercohomology of
the underlying complex of abelian sheaves.

## Main results

* `Stacks.Cech.Hypercohomology.unitD_comp_derivedSectionsFunctorIso`: the unit of the bounded
  below model of derived sections, carried to the unbounded model, is the unbounded unit.
* `Stacks.Cech.Hypercohomology.cechClass_augmentation`: the Čech class of the restriction of a
  global cocycle is its class through the unit.
* `Stacks.Cech.Hypercohomology.cechClass_augmentation_eq_globalClass`: the same in the unbounded
  model.
* `Stacks.Cech.Hypercohomology.realizationUnbounded_abelianGlobalClass_eq_cechClass`: the same
  across the realization comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.RightDerivedBoundary (unitD)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The bounded below unit, in the unbounded model.** The canonical map from ordinary to
derived sections of the bounded below model, followed by the comparison of the bounded below and
the unbounded models of derived global sections, is the unbounded unit. -/
theorem unitD_comp_derivedSectionsFunctorIso (V : AlgebraicGeometry.RingedSpace.{u, u})
    (K : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    unitD (SheafOfModules.evaluation.{u} (structureSheafRing V) (op ⊤)) K ≫
        (Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).hom.app K =
      sectionsUnitQ V ⊤ K.obj := by
  have hn := (Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso V ⊤).hom.naturality
    ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} (structureSheafRing V))).hom.app K)
  have hb := Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso_hom_app V ⊤
    ((HomotopyCategory.Plus.quotient _).obj K)
  have hq : DerivedCategory.Plus.ι.map ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
      (SheafOfModules.{u} (structureSheafRing V))).hom.app K) =
      (DerivedCategory.quotientCompQhIso _).hom.app K.obj :=
    (StacksDraft.DerivedSectionsComparison.liftNatIso_hom_app _ _ _ _ K).trans rfl
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (_ ≫ ·) hn).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) hb).trans ?_
  exact congrArg (fun z => _ ≫ (derivedSectionsOverOpen V ⊤).map z) hq

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {ι : Type u} (U : ι → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- **The Čech class of the restriction of a global cocycle** is its class through the unit
`Γ(X, -) ⟶ RΓ(X, -)` ([Stacks, Tags 07M9, 08BN]). -/
theorem cechClass_augmentation (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (n : ℤ)
    (s : ((Stacks.Cech.Linear.sectionsComplexFunctor X (ringSheaf O) ⊤).obj K.obj).cycles n) :
    (cechClass O U hU K n).hom ((HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU).app K.obj) n).hom
        ((((Stacks.Cech.Linear.sectionsComplexFunctor X (ringSheaf O) ⊤).obj K.obj).homologyπ
          n).hom s)) =
      ((((Stacks.Cech.Linear.sectionsComplexFunctor X (ringSheaf O) ⊤).obj K.obj).homologyπ n ≫
        (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
        (DerivedCategory.homologyFunctor _ n).map
          (Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ K))).hom s := by
  have h1 := (DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n).inv.naturality
      ((Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU).app K.obj)
  have h2 := Stacks.Cech.Linear.sectionsToTotalCechDerived_comp_totalCechToDerivedSections X
    (ringSheaf O) ⊤ U hU K
  have h3 : HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU).app K.obj) n ≫
      cechClass O U hU K n =
      (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
        (DerivedCategory.homologyFunctor _ n).map
          (Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ K) := by
    dsimp only [cechClass]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) h1).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    exact (Functor.map_comp _ _ _).symm.trans (congrArg _ h2)
  exact (ConcreteCategory.congr_hom (congrArg (_ ≫ ·) h3) s).trans rfl

/-- **The Čech class of the restriction of a global cocycle, in the unbounded model**: carried
to the unbounded model of derived global sections, it is the class of the cocycle. -/
theorem cechClass_augmentation_eq_globalClass (V : AlgebraicGeometry.RingedSpace.{u, u})
    {ι : Type u} (U : ι → Opens V.carrier) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ)
    (s : (sectionsComplex V K.obj).cycles n) :
    ((DerivedCategory.homologyFunctor _ n).map
        ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).hom.app K)).hom
      ((cechClass V.sheaf U hU K n).hom ((HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech V.carrier (ringSheaf V.sheaf) ⊤ U hU).app K.obj)
          n).hom (((sectionsComplex V K.obj).homologyπ n).hom s))) =
      globalClass K.obj n s := by
  refine (congrArg _ (cechClass_augmentation V.sheaf U hU K n s)).trans ?_
  have h : Stacks.Cech.Linear.sectionsToDerived V.carrier (ringSheaf V.sheaf) ⊤ K ≫
      (Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).hom.app K =
      sectionsUnitQ V ⊤ K.obj :=
    (congrArg (· ≫ _) (sectionsToDerived_eq_unitD V.sheaf K)).trans
      (unitD_comp_derivedSectionsFunctorIso V K)
  have h2 := (Functor.map_comp (DerivedCategory.homologyFunctor _ n) _ _).symm.trans
    (congrArg _ h)
  exact ConcreteCategory.congr_hom (congrArg (fun z => (sectionsComplex V K.obj).homologyπ n ≫
    (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫ z) h2) s

/-- **The Čech class of a global cocycle across the realization comparison** ([Stacks,
Tag 01F1]): the class of a global cocycle of the underlying complex of abelian sheaves is carried
by `realizationUnbounded` to the Čech class of the restriction of the same section. -/
theorem realizationUnbounded_abelianGlobalClass_eq_cechClass
    (V : AlgebraicGeometry.RingedSpace.{u, u})
    {ι : Type u} (U : ι → Opens V.carrier) (hU : ⊤ = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ)
    (sA : ((sectionsFunctor V.carrier ⊤).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj K)).obj.cycles n)
    (s : (sectionsComplex V K.obj).cycles n)
    (h : (((sectionsFunctor V.carrier ⊤).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj K)).obj.iCycles
        n).hom sA = ((sectionsComplex V K.obj).iCycles n).hom s) :
    (realizationUnbounded V K n).hom.hom
        (abelianGlobalClass
          ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj K) n sA) =
      ((DerivedCategory.homologyFunctor _ n).map
        ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).hom.app K)).hom
      ((cechClass V.sheaf U hU K n).hom ((HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech V.carrier (ringSheaf V.sheaf) ⊤ U hU).app K.obj)
          n).hom (((sectionsComplex V K.obj).homologyπ n).hom s))) :=
  (realizationUnbounded_abelianGlobalClass K n sA s h).trans
    (cechClass_augmentation_eq_globalClass V U hU K n s).symm

/-- **Classes of global cocycles are natural** in the bounded below complex of abelian sheaves:
`RΓ(Y, φ)` sends the class of a global cocycle `s` to the class of its image. -/
theorem abelianGlobalClass_naturality {Y : TopCat.{u}} {L L' : CochainComplex.Plus (AbelianSheaf Y)}
    (φ : L ⟶ L') (n : ℤ)
    (s : ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj.cycles n) :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ))).hom
        (abelianGlobalClass L n s) =
      abelianGlobalClass L' n (HomologicalComplex.cyclesMap
        ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ).hom n s) := by
  have hu := (Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).naturality φ
  have hf := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.naturality
    ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ).hom
  have hπ := HomologicalComplex.homologyπ_naturality
    ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ).hom n
  have h1 : (DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L) ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) =
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (DerivedCategory.Plus.Q.map ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ)) ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L') := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ hu.symm
  have h2 : (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.app
        ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (DerivedCategory.Plus.Q.map ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ)) =
      HomologicalComplex.homologyMap ((sectionsFunctor Y ⊤).mapCochainComplexPlus.map φ).hom n ≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.app
        ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L').obj :=
    hf.symm
  refine (ConcreteCategory.congr_hom h1 _).trans ?_
  refine congrArg ((DerivedCategory.Plus.homologyFunctor _ n).map
    ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L')).hom ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact congrArg ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.app
    ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L').obj).hom
    (ConcreteCategory.congr_hom hπ s)

end Stacks.Cech.Hypercohomology

end
