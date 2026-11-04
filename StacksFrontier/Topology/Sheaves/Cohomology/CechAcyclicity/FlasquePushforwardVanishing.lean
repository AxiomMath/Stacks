module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Flasque sheaves of modules are acyclic for pushforward

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a sheaf of `O_X`-modules whose
underlying sheaf of abelian groups is flasque. Tag 09T0 says that all positive higher direct
images `R^p f_* F` vanish.

The proof reduces to the absolute case. The `i`-th cohomology sheaf of the derived pushforward
is the sheafification of the presheaf `V ↦ H^i(f⁻¹ V, F)` (Tag 01E4), so it suffices that this
presheaf vanishes, i.e. that `F` is acyclic for sections over every open. Acyclicity for
sections of a sheaf of *modules* over an open is Tag 09SY; what has to be added is that it may
be computed after forgetting to abelian groups, which holds because the forgetful functor
`Mod R ⥤ Ab` is exact, hence its own right derived functor, and composites of derived functors
may be evaluated one at a time at an object acyclic for the inner functor.

## Main results

* `Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque`:
  the positive higher direct images of a flasque sheaf of modules are zero.

## Implementation notes

The higher direct image `R^p f_*` is `Functor.rightDerivedPlus p` of the module pushforward
functor, and vanishing is expressed by `CategoryTheory.IsZero` rather than by an equality with
a chosen zero object. Flasqueness is imposed on the underlying sheaf of abelian groups, as in
the source.

`HasDerivedCategory.standard` is made a local instance because there is no global one.

## References

* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.Cohomology.FlasqueAcyclic

namespace Stacks.Cohomology.FlasquePushforward

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

-- Seated from `PushforwardOfAnInjective`, not restated. The `Abelian` instance in particular is a
-- memoising shortcut: without it the same goal inside the `HasRightDerivedFunctor` elaboration
-- exhausts its 20000-heartbeat budget rather than failing to synthesize.
attribute [local instance]
  Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
private lemma map_plus_quasiIso_of_preservesHomology
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] [G.PreservesHomology]
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y)
    (hf : HomotopyCategory.Plus.quasiIso A f) :
    HomotopyCategory.Plus.quasiIso B (G.mapHomotopyCategoryPlus.map f) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective X
  obtain ⟨L, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective Y
  obtain ⟨g, rfl⟩ := (HomotopyCategory.Plus.quotient A).map_surjective f
  rw [HomotopyCategory.Plus.quasiIso_iff, HomotopyCategory.Plus.quotient_map_hom] at hf
  have : QuasiIso g.hom := (HomotopyCategory.quotient_map_mem_quasiIso_iff g.hom).1 hf
  rw [HomotopyCategory.Plus.quasiIso_iff]
  dsimp only [Functor.mapHomotopyCategoryPlus, ObjectProperty.lift_map,
    ObjectProperty.homMk_hom, Functor.comp_map, ObjectProperty.ι_map,
    HomotopyCategory.Plus.quotient_map_hom]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    (HomologicalComplex.quasiIso_map_of_preservesHomology g.hom G)

private lemma rightDerivedFunctorPlusUnit_isIso_of_preservesHomology
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive] [EnoughInjectives A] [G.PreservesHomology] :
    IsIso G.rightDerivedFunctorPlusUnit := by
  have hW : (HomotopyCategory.Plus.quasiIso A).IsInvertedBy
      (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := by
    intro X Y f hf
    exact Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B)
      (G.mapHomotopyCategoryPlus.map f) (map_plus_quasiIso_of_preservesHomology G f hf)
  exact Functor.isIso_of_isRightDerivedFunctor_of_inverts G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit hW

private lemma forget_rightDerivedFunctorPlusUnit_isIso {R : Type u} [Ring R] :
    IsIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlusUnit := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have : G.PreservesHomology := by
    have : PreservesFiniteLimits G := inferInstance
    have : PreservesFiniteColimits G := inferInstance
    exact Functor.preservesHomologyOfExact G
  exact rightDerivedFunctorPlusUnit_isIso_of_preservesHomology G

private lemma isZero_sectionsDerivedPlus_of_isFlasque
    {X : RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X))
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj F)]
    (U : Opens X.carrier) (i : ℤ) (hi : 0 < i) :
    IsZero (((secF (structureSheafRing X) U).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).obj
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj F))) := by
  let E := SheafOfModules.evaluation (structureSheafRing X) (op U)
  let G := forget₂ (ModuleCat.{u}
    ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}
  let S := E ⋙ G
  let K := (HomotopyCategory.Plus.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X)) 0).obj F
  have : E.Additive := evaluation_additive
    (R := structureSheafRing X) (op U)
  let Eplus := E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  have : Eplus.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules
        (structureSheafRing X))) :=
    (HomotopyCategory.Plus.localizerMorphism_derives Eplus).hasPointwiseRightDerivedFunctor
  have : Eplus.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules
        (structureSheafRing X))) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor Eplus _
  have hE : E.rightAcyclic F :=
    rightAcyclic_evaluation_of_isFlasque (F := F) (U := U)
      (R := structureSheafRing X) (by infer_instance)
  have : IsIso G.rightDerivedFunctorPlusUnit := forget_rightDerivedFunctorPlusUnit_isIso
  let β : S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ E.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl S)).inv
        DerivedCategory.Plus.Qh ≫
      Functor.whiskerLeft E.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
      Functor.whiskerRight E.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus
  let t := S.rightDerivedFunctorPlus.rightDerivedDesc S.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso (SheafOfModules (structureSheafRing X)))
    (E.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) β
  have ht : S.rightDerivedFunctorPlusUnit ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh t = β :=
    Functor.rightDerived_fac _ _ _ _ _
  have : IsIso t := (Functor.isIso_iff_rightAcyclic_obj_injective E G t ht).2 fun I _ =>
    NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnit _
  have hβ : IsIso (β.app K) := by
    dsimp [β]
    have hcoh : IsIso (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl S)).inv.app K)) := by
      infer_instance
    have hG : IsIso (G.rightDerivedFunctorPlusUnit.app (E.mapHomotopyCategoryPlus.obj K)) :=
      NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnit _
    have : IsIso (E.rightDerivedFunctorPlusUnit.app K) := hE
    exact IsIso.comp_isIso' hcoh (IsIso.comp_isIso' hG inferInstance)
  have hfac : S.rightDerivedFunctorPlusUnit.app K ≫
      t.app (DerivedCategory.Plus.Qh.obj K) = β.app K := by
    simpa using congrArg (fun α => α.app K) ht
  have : IsIso (S.rightDerivedFunctorPlusUnit.app K) := IsIso.of_isIso_fac_right hfac
  have hsingle : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).obj
      ((DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u} 0).obj (S.obj F))) :=
    DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i hi
  have hsource : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).obj
      ((S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj K)) :=
    IsZero.of_iso hsingle ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).mapIso
      ((Functor.mapSingleFunctorCompQhIso S).app F))
  exact IsZero.of_iso hsource
    (asIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
      (S.rightDerivedFunctorPlusUnit.app K))).symm

private lemma isZero_preimageHypercohomologyPresheaf_of_isFlasque
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj F)]
    (i : ℤ) (hi : 0 < i) :
    IsZero (preimageHypercohomologyPresheaf f
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)) i) := by
  let K := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)
  let P := preimageHypercohomologyPresheaf f K i
  have hPobj (V : (Opens Y.carrier)ᵒᵖ) : IsZero (P.obj V) := by
    let U := (RingedSpaceModuleAdjunction.opensMap f).obj V.unop
    let G := forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj V))
      AddCommGrpCat.{u}
    have hgroups : IsZero (((RingedSpaceModuleAdjunction.modulePushforward f ⋙
        SheafOfModules.forget (structureSheafRing Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (PresheafOfModules (structureSheafRing Y).obj) i ⋙
        PresheafOfModules.toPresheaf (structureSheafRing Y).obj ⋙
        (evaluation (Opens Y.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op V.unop)).obj K) :=
      IsZero.of_iso (isZero_sectionsDerivedPlus_of_isFlasque F U i hi)
        ((preimageHypercohomologyPresheaf_evaluation_iso f V.unop i).app K)
    have hgroups' : IsZero (G.obj (P.obj V)) := by
      show IsZero (((PresheafOfModules.toPresheaf
        (structureSheafRing Y).obj).obj
          ((DerivedCategory.Plus.homologyFunctor
            (PresheafOfModules (structureSheafRing Y).obj) i).obj
            ((RingedSpaceModuleAdjunction.modulePushforward f ⋙
                SheafOfModules.forget
                  (structureSheafRing Y)).rightDerivedFunctorPlus.obj
              K))).obj V)
      exact hgroups
    exact (IsZero.iff_id_eq_zero _).mpr
      (G.map_injective (by simpa using (IsZero.iff_id_eq_zero _).mp hgroups'))
  exact (IsZero.iff_id_eq_zero _).mpr
    (PresheafOfModules.hom_ext fun V => (IsZero.iff_id_eq_zero _).mp (hPobj V))

/-- A flasque sheaf of modules has vanishing positive higher direct images under any
morphism of ringed spaces. -/
@[stacks 09T0, sga "4 V 5.2" "special case"]
public lemma isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj F)]
    (p : ℤ) (hp : 0 < p) :
    IsZero (((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedPlus p).obj F) := by
  let K := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)
  have hQh : IsZero (((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ p).obj K) :=
    IsZero.of_iso
      (Functor.map_isZero (PresheafOfModules.sheafification
        (𝟙 (structureSheafRing Y).obj))
        (isZero_preimageHypercohomologyPresheaf_of_isFlasque f F p hp))
      ((derivedPushforwardPlus_homology_iso_sheafify_preimageHypercohomology f p).app K)
  have eTarget :
      (((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ p).obj K) ≅
      (((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedPlus p).obj F) :=
    ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ p).mapIso
        ((Functor.mapSingleFunctorCompQhIso
          (𝟭 (SheafOfModules.{u} (structureSheafRing X)))).app F)
  exact IsZero.of_iso hQh eTarget.symm

end Stacks.Cohomology.FlasquePushforward
