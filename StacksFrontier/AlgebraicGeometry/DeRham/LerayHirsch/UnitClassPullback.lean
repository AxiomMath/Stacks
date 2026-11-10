module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.HomologyPullback

/-!
# The class of the unit across a direct image

Let `h : W' ⟶ W` be a morphism of ringed spaces. The structure map `𝒪_W ⟶ h_*𝒪_{W'}`, placed in
degree `m` and followed by the comparison `h_* ⟶ Rh_*`, is a morphism

`v_h : 𝒪_W[-m] ⟶ Rh_*(𝒪_{W'}[-m])`

of `D(𝒪_W)`. Through the Leray identification `H^m(W, Rh_* -) = H^m(W', -)` of
[Stacks, Tag 0D5W] it carries the class of the unit section `1` to the class of `1`
(`lerayCohomologyIso_unitToPushforward`). Composing with `Rh_*` of a morphism
`γ : 𝒪_{W'}[-m] ⟶ K` therefore produces a morphism `𝒪_W[-m] ⟶ Rh_*K` whose value at the unit is
the value of `γ` at the unit (`lerayCohomologyIso_evalUnit_classPushforward`). This is how a de
Rham class on `X`, read in `D(f^{-1}𝒪_Y)`, becomes the morphism `𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` of
[Stacks, Tag 0FMP].

## Main definitions

* `Stacks.Cohomology.UnitClassPullback.unitToPushforward`: the morphism of complexes
  `𝒪_W[-m] ⟶ h_*(𝒪_{W'}[-m])`.
* `Stacks.Cohomology.UnitClassPullback.unitToDerivedPushforward`: `v_h`.
* `Stacks.Cohomology.UnitClassPullback.classPushforward`: `v_h ≫ Rh_*γ`.

## Main results

* `Stacks.Cohomology.UnitClassPullback.lerayCohomologyIso_unitToPushforward`.
* `Stacks.Cohomology.UnitClassPullback.lerayCohomologyIso_evalUnit_classPushforward`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.HomologyPullback (map_map_comp_apply)

universe u

namespace Stacks.Cohomology.UnitClassPullback

attribute [local instance] HasDerivedCategory.standard

variable {W' W : RingedSpace.{u, u}} (h : W' ⟶ W) (m : ℤ)

/-- The unit section of `h_*(𝒪_{W'}[-m])` in degree `m` is a cocycle: the complex is concentrated
in degree `m`. -/
theorem d_unitSection_pushforward :
    ((((pushforwardComplex h).obj (unitComplex W' m)).d m (m + 1)).val.app (op ⊤)).hom
      (unitSection W' m) = 0 := by
  have : ((pushforwardComplex h).obj (unitComplex W' m)).d m (m + 1) = 0 := by
    change (StacksDraft.KFlat.modulePushforward h).map ((unitComplex W' m).d m (m + 1)) = 0
    rw [show (unitComplex W' m).d m (m + 1) = 0 by simp [unitComplex]]
    exact (modulePushforward h).map_zero _ _
  rw [this]
  rfl

/-- **The structure map `𝒪_W ⟶ h_*𝒪_{W'}`, placed in degree `m`**, as a morphism of complexes:
the morphism out of the unit sending the section `1` to the section `1`. -/
def unitToPushforward : unitComplex W m ⟶ (pushforwardComplex h).obj (unitComplex W' m) :=
  homOfCycle ((pushforwardComplex h).obj (unitComplex W' m)) m (unitSection W' m)
    (d_unitSection_pushforward h m)

/-- **`v_h : 𝒪_W[-m] ⟶ Rh_*(𝒪_{W'}[-m])`**: the structure map, placed in degree `m`, followed by
the comparison of the direct image with the derived direct image. -/
def unitToDerivedPushforward :
    DerivedCategory.Q.obj (unitComplex W m) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).obj
        (DerivedCategory.Q.obj (unitComplex W' m)) :=
  DerivedCategory.Q.map (unitToPushforward h m) ≫ pushforwardComparisonQ h (unitComplex W' m)

/-- The structure map sends the unit section in degree `m` to the unit section. -/
theorem unitToPushforward_unitSection :
    ((((globalSections W).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (unitToPushforward h m)).f m).hom (unitSection W m) = unitSection W' m :=
  homOfCycle_unitSection _ m _ (d_unitSection_pushforward h m)

/-- **The unit class goes to the unit class.** Through the Leray identification
`H^m(W, Rh_* -) = H^m(W', -)`, the morphism `v_h` carries the class of `1` to the class of `1`. -/
theorem lerayCohomologyIso_unitToPushforward :
    (lerayCohomologyIso h (DerivedCategory.Q.obj (unitComplex W' m)) m).hom
        (((DerivedCategory.homologyFunctor _ m).map
          ((baseSections W).map (unitToDerivedPushforward h m))).hom (unitCycleClass W m)) =
      unitCycleClass W' m := by
  have h₁ := globalClass_map W (unitToPushforward h m) m (unitCycle W m)
  refine (congrArg _ (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ m)
    (DerivedCategory.Q.map (unitToPushforward h m)) (pushforwardComparisonQ h (unitComplex W' m))
    (unitCycleClass W m))).trans ?_
  refine (congrArg _ (congrArg _ h₁)).trans ?_
  refine lerayCohomologyIso_globalClass h (unitComplex W' m) m _ _ ?_
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((globalSections W).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (unitToPushforward h m)) m) (unitCycle W m)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ (iCycles_unitCycle W m)).trans ?_
  exact (unitToPushforward_unitSection h m).trans (iCycles_unitCycle W' m).symm

/-- **A class pushed forward**: for `γ : 𝒪_{W'}[-m] ⟶ K`, the morphism `v_h ≫ Rh_*γ`. -/
def classPushforward {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing W'))}
    (γ : DerivedCategory.Q.obj (unitComplex W' m) ⟶ K) :
    DerivedCategory.Q.obj (unitComplex W m) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).obj K :=
  unitToDerivedPushforward h m ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map γ

/-- **The pushed-forward class evaluates to the class.** Through the Leray identification, the
value at the unit of `v_h ≫ Rh_*γ` is the value at the unit of `γ`. -/
theorem lerayCohomologyIso_evalUnit_classPushforward
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing W'))}
    (γ : DerivedCategory.Q.obj (unitComplex W' m) ⟶ K) :
    (lerayCohomologyIso h K m).hom
        (evalUnit ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).obj K) m
          (classPushforward h m γ)) =
      evalUnit K m γ := by
  have hn := lerayCohomologyIso_naturality_apply h γ m
    (((DerivedCategory.homologyFunctor _ m).map
      ((baseSections W).map (unitToDerivedPushforward h m))).hom (unitCycleClass W m))
  rw [lerayCohomologyIso_unitToPushforward] at hn
  refine Eq.trans ?_ hn
  exact congrArg _ (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ m)
    (unitToDerivedPushforward h m)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map γ)
    (unitCycleClass W m))

end Stacks.Cohomology.UnitClassPullback

end
