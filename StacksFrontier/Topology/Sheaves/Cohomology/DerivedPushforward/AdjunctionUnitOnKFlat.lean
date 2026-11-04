module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# The derived unit of `Lf^* ⊣ Rf_*`, computed on a K-flat complex

For a morphism of ringed spaces `f : X ⟶ Y`, this file computes the unit of the derived adjunction
`Lf^* ⊣ Rf_*` of Tag 079W at an object `Qh.obj M` of the derived category, provided the
comparison `Lf^* (Qh M) ⟶ Qh (f^* M)` is invertible at `M`; this is the case when `M` is K-flat,
by Stacks 06YJ.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_eq_of_iso`: at
  `Qh.obj M` the derived unit is the derived image of the homotopy-category unit, followed by the
  pushforward-side comparison, followed by the derived pushforward of the inverse of the
  pullback-side comparison at `M`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_eq_of_isKFlat`:
  the same for a K-flat `M`, with the inverse of the pullback-side comparison.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- At an object of the form `Qh.obj M`, given an isomorphism `e` whose forward map is the
pullback-side comparison at `M`, the unit `Qh M ⟶ Rf_* (Lf^* (Qh M))` of `Lf^* ⊣ Rf_*` is

`Qh (underived unit) ≫ (pushforward comparison at f^* M) ≫ Rf_* e.inv`. -/
theorem derivedAdjunction_unit_app_eq_of_iso
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (e : (DerivedCategory.Qh ⋙ derivedPullback f).obj M ≅ (pullbackOnHomotopy f).obj M)
    (he : e.hom = (derivedPullbackComparison f).app M) :
    (derivedAdjunction f).unit.app (DerivedCategory.Qh.obj M) =
      (DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
          (derivedPushforwardUnit f).app
            (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward f).map e.inv := by
  refine ((derivedPushforward f).mapIso e).eq_comp_inv.mpr ?_
  simp only [Functor.mapIso_hom, he]
  exact derivedAdjunction_unit_fac f M

/-- On a K-flat object `M` of the homotopy category, the unit of `Lf^* ⊣ Rf_*` at `Qh.obj M` is

`Qh (underived unit) ≫ (pushforward comparison at f^* M) ≫ Rf_* (pullback comparison at M)⁻¹`. -/
theorem derivedAdjunction_unit_app_eq_of_isKFlat
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (hM : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y M) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_isKFlat
      f M hM
    (derivedAdjunction f).unit.app (DerivedCategory.Qh.obj M) =
      (DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
          (derivedPushforwardUnit f).app
            (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward f).map (inv ((derivedPullbackComparison f).app M)) :=
  let := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_isKFlat
    f M hM
  derivedAdjunction_unit_app_eq_of_iso f M (asIso ((derivedPullbackComparison f).app M)) rfl

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end

end
