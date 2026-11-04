module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pushforward commutes with derived limits

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. Then `Rf_*` commutes with
derived limits: if a distinguished triangle exhibits `L` as the derived limit of an inverse
system `(K_n)` of objects of `D(𝒪_X)`, then `Rf_* L` is the derived limit of the inverse system
`(Rf_* K_n)`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunctionOfIsRightDerivedFunctor`:
  the derived pullback is a left adjoint of any right derived functor of degreewise pushforward.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isDerivedLimit_map_derivedPushforward`:
  the derived pushforward carries a derived limit to a derived limit.

## Implementation notes

The derived pushforward enters as an arbitrary functor equipped with the universal property of
the right derived functor of degreewise pushforward, so the result does not depend on a choice
of resolutions; the existence of the product in the target is part of the conclusion rather than
a hypothesis.

## References

* [Stacks Project, Tag 0BKP](https://stacks.math.columbia.edu/tag/0BKP)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (α : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]

/-- The derived pullback `Lf^*` is a left adjoint of every right derived functor of degreewise
pushforward. -/
def derivedAdjunctionOfIsRightDerivedFunctor : derivedPullback f ⊣ Rf :=
  (derivedAdjunction f).ofNatIsoRight
    (Functor.rightDerivedUnique (derivedPushforward f) Rf (derivedPushforwardUnit f) α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))

include f α in
/-- Derived pushforward along a morphism of ringed spaces commutes with derived limits: it carries
an object exhibited as the derived limit of a countable inverse system to the derived limit of the
pushed-forward system. -/
@[stacks 0BKP]
theorem isDerivedLimit_map_derivedPushforward
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ Rf.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) _ _ _ _ _ _
        (K ⋙ Rf) h (Rf.obj L) := by
  obtain ⟨p, δ, hT⟩ := hL
  have _ : PreservesLimitsOfSize.{0, 0} Rf :=
    (derivedAdjunctionOfIsRightDerivedFunctor f Rf α).rightAdjoint_preservesLimits
  let h : HasProduct (fun n : ℕ ↦ Rf.obj (K.obj ⟨n⟩)) :=
    ⟨⟨_, isLimitOfHasProductOfPreservesLimit Rf (fun n : ℕ ↦ K.obj ⟨n⟩)⟩⟩
  let _ := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  have _ : Rf.IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward f) Rf α
  exact ⟨h, Rf.map p ≫ piComparison Rf (fun n : ℕ ↦ K.obj ⟨n⟩),
    Stacks.Injectives.isDerivedLimit_map_of_preservesProduct Rf K L p ⟨δ, hT⟩⟩

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
