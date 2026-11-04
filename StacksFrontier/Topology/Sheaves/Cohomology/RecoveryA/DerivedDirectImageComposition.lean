module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived direct images

For composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the total derived
direct image of the composite is canonically isomorphic to the composite of the total derived
direct images, on bounded below derived categories of sheaves of modules.

## Main definitions

* `Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesComparison` is the
  canonical comparison from the derived direct image of a composite to the composite of the
  derived direct images.
* `Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesCompIso` is the
  resulting natural isomorphism.
* `Stacks.Cohomology.DerivedDirectImageComposition.rightDerivedEvaluationForgetIsoOfOpens`
  identifies the right derived functors of sections over an open before and after forgetting
  the module structure.

## Main results

* `Stacks.Cohomology.DerivedDirectImageComposition.higherDirectImagesComparison_isIso` says
  that the canonical comparison is an isomorphism.

## Implementation notes

The total derived direct image along `f` is Mathlib's
`(pushforward f).rightDerivedFunctorPlus`. The comparison is characterized by the universal
property of this right derived functor: before deriving, it is the composite of the ordinary
pushforward-composition isomorphism of Stacks 0097 and the two derived-functor units. Thus
the statement records the canonical comparison, not merely the existence of some isomorphism.
In Lean's diagrammatic order, `Rf_*` followed by `Rg_*` is written `Rf_* ⋙ Rg_*`.

That the comparison is invertible is `Functor.isIso_iff_rightAcyclic_obj_injective`: it holds
as soon as `f_*I` is right acyclic for `g_*` whenever `I` is injective. That acyclicity is
proved by passing to sections: the higher direct images are the sheafifications of the
presheaves `V ↦ Hⁿ(g⁻¹V, -)` (Stacks 01E4), those values are the higher derived functors of
evaluation, an injective sheaf of modules has surjective restriction maps (Stacks 01EA) so
`f_*I` is flasque, and a flasque sheaf is acyclic for evaluation (Stacks 09SY).

Two parallel presentations of pushforward meet here and are definitionally the same: the
ringed-space functors `Modules`/`pushforward` of
`StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`, in terms of which the statement is
phrased, and `structureSheafRing`/`modulePushforward`, in terms of which
Tags 01E4, 01EA and 09SY are stated and which the proof therefore uses.

## References

* [Stacks Project, Tag 01F5](https://stacks.math.columbia.edu/tag/01F5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Cohomology.HigherDirectImagePresheaf

universe wX wY wZ u

namespace Stacks.Cohomology.DerivedDirectImageComposition

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

-- Seated from `PushforwardOfAnInjective`, not restated. The `Abelian` one is a memoising
-- shortcut: removing it alone reproduces a 20000-heartbeat typeclass timeout in that file.
attribute [local instance]
  Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian

/-- Pushforward of sheaves of modules along a morphism of ringed spaces is additive. -/
noncomputable instance pushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (pushforward f).Additive where
  map_add := rfl

/-- The canonical comparison
`R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*` on bounded below derived categories.

It is the unique map from the right derived functor whose composite with its
unit is obtained from the ordinary pushforward-composition isomorphism and the
units for the derived direct images along `f` and `g`. -/
noncomputable def higherDirectImagesComparison {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (Modules X)]
    [HasDerivedCategory.{wY} (Modules Y)]
    [HasDerivedCategory.{wZ} (Modules Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward (f ≫ g)).rightDerivedFunctorPlus ⟶
      (pushforward f).rightDerivedFunctorPlus ⋙
        (pushforward g).rightDerivedFunctorPlus :=
  (pushforward (f ≫ g)).rightDerivedFunctorPlus.rightDerivedDesc
    (pushforward (f ≫ g)).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso (Modules X)) _
    (Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso (pushforwardComp f g).symm).inv
          DerivedCategory.Plus.Qh ≫
      Functor.whiskerLeft (pushforward f).mapHomotopyCategoryPlus
        (pushforward g).rightDerivedFunctorPlusUnit ≫
      Functor.whiskerRight (pushforward f).rightDerivedFunctorPlusUnit
        (pushforward g).rightDerivedFunctorPlus)

universe wA wB

private lemma rightAcyclic_iff_rightDerivedNat
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wB} D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)] (A : C) :
    F.rightAcyclic A ↔ ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj A) := by
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F A).2 inferInstance]
  refine ⟨fun h n hn => (h n (by omega)).of_iso (derivedPlusToStandardObj F A n).symm,
    fun h i hi => ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact (h n (by omega)).of_iso (derivedPlusToStandardObj F A n)

private noncomputable def rightDerivedEvaluationForgetIso
    {X : RingedSpace.{u, u}} (U : Opens X.carrier) (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (forget₂ (ModuleCat.{u}
      ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation (structureSheafRing X)
          (op U)).rightDerived n).obj M) ≅
      (((SheafOfModules.evaluation (structureSheafRing X) (op U)) ⋙
        forget₂ (ModuleCat.{u}
          ((structureSheafRing X).obj.obj (op U)))
            AddCommGrpCat.{u}).rightDerived n).obj M := by
  let I := injectiveResolution M
  let E := SheafOfModules.evaluation (structureSheafRing X) (op U)
  let G := forget₂ (ModuleCat.{u}
    ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact G.mapIso (I.isoRightDerivedObj E n) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ n).app K) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ n).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (E ⋙ G) n).symm


/-- Forgetting the module structure commutes with the right derived functors of sections, since
both are computed from the same injective resolution. -/
public noncomputable def rightDerivedEvaluationForgetIsoOfOpens
    {X : RingedSpace.{u, u}} (U : Opens X.carrier) (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (forget₂ (ModuleCat.{u}
      ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation (structureSheafRing X)
          (op U)).rightDerived n).obj M) ≅
      (((SheafOfModules.evaluation (structureSheafRing X) (op U)) ⋙
        forget₂ (ModuleCat.{u}
          ((structureSheafRing X).obj.obj (op U)))
            AddCommGrpCat.{u}).rightDerived n).obj M := by
  let I := injectiveResolution M
  let E := SheafOfModules.evaluation (structureSheafRing X) (op U)
  let G := forget₂ (ModuleCat.{u}
    ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact G.mapIso (I.isoRightDerivedObj E n) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ n).app K) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ n).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (E ⋙ G) n).symm

private instance evaluation_hasRightDerivedFunctor (X : RingedSpace.{u, u})
    (V : Opens X.carrier) :
    (((SheafOfModules.evaluation (structureSheafRing X)
      (op V)).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (SheafOfModules (structureSheafRing X)))) := by
  let ev := SheafOfModules.evaluation (structureSheafRing X) (op V)
  let _ : ev.Additive :=
    Stacks.Cohomology.FlasqueAcyclic.evaluation_additive
      (structureSheafRing X) (op V)
  exact Functor.HasRightDerivedFunctor.mk' ev.rightDerivedFunctorPlus
    ev.rightDerivedFunctorPlusUnit

private theorem pushforward_rightDerived_positive_of_injective
    {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Modules X) [Injective I] :
    ∀ n : ℕ, 0 < n →
      IsZero (((pushforward g).rightDerived n).obj ((pushforward f).obj I)) := by
  let M := (pushforward f).obj I
  let OY := structureSheafRing Y
  let OZ := structureSheafRing Z
  let : HasDerivedCategory.{u + 1} (SheafOfModules OY) :=
    HasDerivedCategory.standard (SheafOfModules OY)
  let : HasDerivedCategory.{u + 1} (SheafOfModules OZ) :=
    HasDerivedCategory.standard (SheafOfModules OZ)
  let I' : SheafOfModules.{u} (structureSheafRing X) := I
  let : Injective I' := ‹Injective I›
  let : Abelian (SheafOfModules OY) := inferInstance
  let : EnoughInjectives (SheafOfModules OY) := IsGrothendieckAbelian.enoughInjectives
  have hsec : ∀ U : Opens Y.carrier, ∀ n : ℕ, 0 < n →
      IsZero (((secF OY U).rightDerived n).obj
        ((RingedSpaceModuleAdjunction.modulePushforward f).obj I')) := by
    intro U n hn
    let : HasDerivedCategory.{u + 1} (ModuleCat.{u} (OY.obj.obj (op U))) :=
      HasDerivedCategory.standard (ModuleCat.{u} (OY.obj.obj (op U)))
    let : (SheafOfModules.evaluation OY (op U)).Additive :=
      Stacks.Cohomology.FlasqueAcyclic.evaluation_additive OY (op U)
    let ev := SheafOfModules.evaluation OY (op U)
    let W := HomotopyCategory.Plus.quasiIso (SheafOfModules OY)
    let : (ev.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor W :=
      evaluation_hasRightDerivedFunctor Y U
    exact IsZero.of_iso
      ((forget₂ (ModuleCat.{u} (OY.obj.obj (op U))) AddCommGrpCat.{u}).map_isZero
        ((rightAcyclic_iff_rightDerivedNat ev
          ((RingedSpaceModuleAdjunction.modulePushforward f).obj I')).1
          (Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic f I' U) n hn))
      (rightDerivedEvaluationForgetIsoOfOpens U n
        ((RingedSpaceModuleAdjunction.modulePushforward f).obj I')).symm
  intro n hn
  let : (RingedSpaceModuleAdjunction.modulePushforward g).IsRightAdjoint :=
    RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint g
  let : (RingedSpaceModuleAdjunction.modulePushforward g).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  let cf := cohFunctor.{u, u, u, u, u, u}
    (RingedSpaceModuleAdjunction.opensMap g) OY OZ
    (RingedSpaceModuleAdjunction.structureSheafHom g)
  let : cf.Additive := by
    change (RingedSpaceModuleAdjunction.modulePushforward g ⋙
      SheafOfModules.forget OZ).Additive
    infer_instance
  let Pn := cf.rightDerived n |>.obj M
  have hPn : IsZero Pn := (IsZero.iff_id_eq_zero _).2 <|
    (PresheafOfModules.toPresheaf OZ.obj).map_injective <|
      ((Functor.isZero_iff _).2 fun U =>
        IsZero.of_iso (hsec ((RingedSpaceModuleAdjunction.opensMap g).obj U.unop) n hn)
          ((preimageCohomologyPresheaf_evaluation_iso g U.unop n).app M)).eq_of_src _ _
  exact IsZero.of_iso
    (IsZero.of_iso ((PresheafOfModules.sheafification (𝟙 OZ.obj)).map_isZero hPn)
      ((higherDirectImage_iso_sheafify_preimageCohomology g n).app M))
    (derivedPlusToStandardObj (pushforward g) M n).symm

private theorem pushforward_rightAcyclic_of_injective
    {X Y Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{wX} (Modules X)] [HasDerivedCategory.{wY} (Modules Y)]
    [HasDerivedCategory.{wZ} (Modules Z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Modules X) [Injective I] [PreservesFiniteLimits (pushforward g)]
    [((pushforward g).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Modules Y))] :
    (pushforward g).rightAcyclic ((pushforward f).obj I) := by
  let : Abelian (Modules Y) := by unfold Modules; infer_instance
  let : Abelian (Modules Z) := by unfold Modules; infer_instance
  let : IsGrothendieckAbelian (Modules Y) := by unfold Modules; infer_instance
  let : IsGrothendieckAbelian (Modules Z) := by unfold Modules; infer_instance
  let : EnoughInjectives (Modules Y) := IsGrothendieckAbelian.enoughInjectives
  let : EnoughInjectives (Modules Z) := IsGrothendieckAbelian.enoughInjectives
  let : (pushforward g).Additive := pushforward_additive g
  let : (pushforward g).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  exact (rightAcyclic_iff_rightDerivedNat (pushforward g) ((pushforward f).obj I)).2
    (pushforward_rightDerived_positive_of_injective f g I)

/-- **Stacks Project, Tag 01F5.** The canonical comparison from the derived direct image of a
composite to the composite of the derived direct images is an isomorphism. -/
@[stacks 01F5]
theorem higherDirectImagesComparison_isIso {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (Modules X)]
    [HasDerivedCategory.{wY} (Modules Y)]
    [HasDerivedCategory.{wZ} (Modules Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (higherDirectImagesComparison f g) := by
  let F := pushforward f
  let G := pushforward g
  let P := pushforward (f ≫ g)
  let : Abelian (Modules X) := by unfold Modules; infer_instance
  let : Abelian (Modules Y) := by unfold Modules; infer_instance
  let : Abelian (Modules Z) := by unfold Modules; infer_instance
  let : EnoughInjectives (Modules X) := IsGrothendieckAbelian.enoughInjectives
  let : EnoughInjectives (Modules Y) := IsGrothendieckAbelian.enoughInjectives
  let : EnoughInjectives (Modules Z) := IsGrothendieckAbelian.enoughInjectives
  let : G.Additive := pushforward_additive g
  let : G.IsRightAdjoint := (pullbackPushforwardAdjunction g).isRightAdjoint
  let : PreservesFiniteLimits G := inferInstance
  let : (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Modules Y)) :=
    Functor.HasRightDerivedFunctor.mk' G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnit
  let W' := HomotopyCategory.Plus.quasiIso (Modules X)
  let eKC :=
    (Functor.mapHomotopyCategoryPlusCompIso (pushforwardComp f g).symm).symm ≪≫
      Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))
  let eK := Functor.isoWhiskerRight eKC (DerivedCategory.Plus.Qh)
  let eR := Functor.rightDerivedNatIso P.rightDerivedFunctorPlus
    (F ⋙ G).rightDerivedFunctorPlus P.rightDerivedFunctorPlusUnit
    (F ⋙ G).rightDerivedFunctorPlusUnit W' eK
  let β₀ : (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) := Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      (DerivedCategory.Plus.Qh) ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus
  let t₀ : (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
    (F ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc
      (F ⋙ G).rightDerivedFunctorPlusUnit W' _ β₀
  have ht₀ : (F ⋙ G).rightDerivedFunctorPlusUnit ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh t₀ = β₀ :=
    Functor.rightDerived_fac _ _ _ _ _
  have ht₀iso : IsIso t₀ :=
    (Functor.isIso_iff_rightAcyclic_obj_injective F G t₀ ht₀).2 fun I _ =>
      pushforward_rightAcyclic_of_injective f g I
  have hcomp : higherDirectImagesComparison f g = eR.hom ≫ t₀ := by
    apply Functor.rightDerived_ext P.rightDerivedFunctorPlus
      P.rightDerivedFunctorPlusUnit W' _ _ _
    calc
      P.rightDerivedFunctorPlusUnit ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
          (higherDirectImagesComparison f g) =
        Functor.whiskerRight
            (Functor.mapHomotopyCategoryPlusCompIso (pushforwardComp f g).symm).inv
            DerivedCategory.Plus.Qh ≫
          Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
          Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus :=
        Functor.rightDerived_fac _ _ _ _ _
      _ = eK.hom ≫ β₀ := by
        dsimp [β₀, eK, eKC]
        cat_disch
      _ = eK.hom ≫
          ((F ⋙ G).rightDerivedFunctorPlusUnit ≫
            Functor.whiskerLeft DerivedCategory.Plus.Qh t₀) := by
        rw [← ht₀]
      _ = P.rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh (eR.hom ≫ t₀) := by
        simp [eR, Functor.whiskerLeft_comp]
  rw [hcomp]
  infer_instance

/-- The canonical natural isomorphism
`Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` on bounded below derived categories. -/
noncomputable def higherDirectImagesCompIso {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (Modules X)]
    [HasDerivedCategory.{wY} (Modules Y)]
    [HasDerivedCategory.{wZ} (Modules Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward f).rightDerivedFunctorPlus ⋙
      (pushforward g).rightDerivedFunctorPlus ≅
        (pushforward (f ≫ g)).rightDerivedFunctorPlus :=
  haveI := higherDirectImagesComparison_isIso f g
  (asIso (higherDirectImagesComparison f g)).symm

end Stacks.Cohomology.DerivedDirectImageComposition
