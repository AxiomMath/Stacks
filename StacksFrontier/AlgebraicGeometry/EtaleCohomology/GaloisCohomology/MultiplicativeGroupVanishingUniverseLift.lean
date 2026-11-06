module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ModuleUniverseLift
import StacksCore.Tactic.StacksAttribute

/-!
# The vanishing of `H ¹` and `H ²` of the units at a raised coefficient universe

Let `Ω/K` be a Galois extension. The discrete `Gal(Ω/K)`-module `Ωˣ`, with its coefficient
universe raised to `ULift (Additive Ωˣ)`, has vanishing first continuous group cohomology, and
vanishing second continuous group cohomology when the Brauer group of `K` is trivial.

## Main definitions

* `Stacks.GaloisCohomology.unitsContinuousGModuleLift`: the discrete `Gal(Ω/K)`-module
  `ULift (Additive Ωˣ)`.

## Main results

* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_one`:
  `H ¹(Gal(Ω/K), ULift Ωˣ) = 0`.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_two`:
  `H ²(Gal(Ω/K), ULift Ωˣ) = 0` when `Br(K) = 0`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.GaloisCohomology

/-- The discrete Galois module `Ωˣ` with its coefficient universe raised: the carrier is
`ULift (Additive Ωˣ)` and the action is the Galois action on the units. -/
def unitsContinuousGModuleLift.{u, v} (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] : ContinuousGModule.{u, max u v} Gal(Ω/K) :=
  Stacks.GroupCohomology.uliftContinuousModule.{0, u, u, v} (unitsContinuousGModule K Ω)

/-- The Galois action on the raised module is the action on the unraised one. -/
@[simp] theorem unitsContinuousGModuleLift_ρ_hom.{u, v} (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (g : Gal(Ω/K))
    (a : (unitsContinuousGModuleLift.{u, v} K Ω).obj.obj.V) :
    (((unitsContinuousGModuleLift.{u, v} K Ω).obj.obj.ρ g).asHom.hom a).down =
      ((unitsContinuousGModule K Ω).obj.obj.ρ g).asHom.hom a.down := rfl

/-- `H ¹(Gal(Ω/K), ULift Ωˣ) = 0` as a value of `continuousGroupCohomology.{u, v}`. -/
theorem isZero_continuousGroupCohomology_unitsLift_one.{u, v} (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] :
    IsZero (continuousGroupCohomology.{u, v} Gal(Ω/K) 1
      (unitsContinuousGModuleLift.{u, v} K Ω)) := by
  refine Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary
    (unitsContinuousGModuleLift.{u, v} K Ω) ?_
  intro c hcloc hccoc
  obtain ⟨x, hx⟩ := exists_sub_eq_of_isCocycle_additive_units K Ω (fun g ↦ (c g).down)
    (hcloc.comp fun a ↦ a.down) fun g₁ g₂ ↦ congrArg ULift.down (hccoc g₁ g₂)
  exact ⟨ULift.up x, fun g ↦ ULift.down_injective (hx g)⟩

/-- If `Br(K) = 0` then `H ²(Gal(Ω/K), ULift Ωˣ) = 0` as a value of
`continuousGroupCohomology.{u, v}`. -/
theorem isZero_continuousGroupCohomology_unitsLift_two.{u, v} (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (hBr : ∀ y : BrauerGroup K, y = 1) :
    IsZero (continuousGroupCohomology.{u, v} Gal(Ω/K) 2
      (unitsContinuousGModuleLift.{u, v} K Ω)) := by
  refine Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary
    (unitsContinuousGModuleLift.{u, v} K Ω) ?_
  intro d hdloc hdcoc
  obtain ⟨x, hxloc, hx⟩ := exists_isLocallyConstant_sub_eq_of_isCocycle₂_additive_units K Ω hBr
    (fun p ↦ (d p).down) (hdloc.comp fun a ↦ a.down)
    fun g₁ g₂ g₃ ↦ congrArg ULift.down (hdcoc g₁ g₂ g₃)
  exact ⟨fun g ↦ ULift.up (x g), hxloc.comp ULift.up,
    fun g₁ g₂ ↦ ULift.down_injective (hx g₁ g₂)⟩

end Stacks.GaloisCohomology

end
