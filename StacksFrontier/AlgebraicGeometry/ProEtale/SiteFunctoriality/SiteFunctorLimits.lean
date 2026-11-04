module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Limit preservation by the pro-étale site functors

The functors between pro-étale sites are built from two pieces: composing the structure
morphism of a slice object with a fixed morphism of the base, and including the small
pro-étale site of a scheme into the big slice over it. This file records the limits each
piece preserves, which is what makes them continuous and makes the induced inverse images
left exact.

Composition along `f : T ⟶ S` preserves all connected limits, because the slice-forgetful
functors create them and composition commutes with forgetting. The small-site inclusion
preserves fibre products and equalizers, because the underlying-scheme functor of the small
site creates them and the inclusion of the chosen big category into schemes is fully
faithful.

## Main results

* `AlgebraicGeometry.ProEtale.overMap_preservesLimitsOfShape_of_isConnected`
* `AlgebraicGeometry.ProEtale.smallProetaleInclusion_preservesPullbacks`
* `AlgebraicGeometry.ProEtale.smallProetaleInclusion_preservesEqualizers`

## References

* [Stacks Project, Tag 098Q](https://stacks.math.columbia.edu/tag/098Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- Composing the structure morphism of a slice object with `f : T ⟶ S` preserves connected
limits, since the slice-forgetful functor of `S` creates them and sends composition along `f`
to the slice-forgetful functor of `T`. -/
public instance overMap_preservesLimitsOfShape_of_isConnected
    (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)
    {I : Type*} [Category I] [IsConnected I] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I ((Over.map f) ⋙ Over.forget S) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map f) (Over.forget S)

/-- Fibre products in the small pro-étale site remain fibre products in the
big pro-étale slice. -/
@[stacks 098Q "preservation of fibre products"]
public instance smallProetaleInclusion_preservesPullbacks
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan (SmallProetale.inclusion B S hS) := by
  let : CreatesLimitsOfShape WalkingCospan (SmallProetale.toScheme B S hS) :=
    smallProetale_createsPullbacks B S hS
  have hscheme : PreservesLimitsOfShape WalkingCospan
      ((SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS) ⋙
        B.inclusion) := by
    change PreservesLimitsOfShape WalkingCospan (SmallProetale.toScheme B S hS)
    infer_instance
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS ⋙ BigProetaleOver.toScheme B S hS) := hscheme
  have hforget : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS) := by
    let : B.inclusion.Full := inferInstance
    let : B.inclusion.Faithful := inferInstance
    let : ReflectsLimitsOfShape WalkingCospan B.inclusion :=
      (fullyFaithful_reflectsLimits B.inclusion).reflectsLimitsOfShape
    exact preservesLimitsOfShape_of_reflects_of_preserves _ B.inclusion
  let : PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS) := hforget
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (SmallProetale.inclusion B S hS) (BigProetaleOver.forget B S hS)

/-- Equalizers in the small pro-étale site remain equalizers in the big pro-étale slice. -/
public instance smallProetaleInclusion_preservesEqualizers
    (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingParallelPair (SmallProetale.inclusion B S hS) := by
  have hscheme : PreservesLimitsOfShape WalkingParallelPair
      (SmallProetale.inclusion B S hS ⋙
        Over.forget (⟨S, hS⟩ : B.Scheme) ⋙ B.inclusion) := by
    change PreservesLimitsOfShape WalkingParallelPair (SmallProetale.toScheme B S hS)
    infer_instance
  let : PreservesLimitsOfShape WalkingParallelPair
      ((SmallProetale.inclusion B S hS ⋙
        Over.forget (⟨S, hS⟩ : B.Scheme)) ⋙ B.inclusion) := hscheme
  have hforget : PreservesLimitsOfShape WalkingParallelPair
      (SmallProetale.inclusion B S hS ⋙ Over.forget (⟨S, hS⟩ : B.Scheme)) := by
    let : B.inclusion.Full := inferInstance
    let : B.inclusion.Faithful := inferInstance
    let : ReflectsLimitsOfShape WalkingParallelPair B.inclusion :=
      (fullyFaithful_reflectsLimits B.inclusion).reflectsLimitsOfShape
    exact preservesLimitsOfShape_of_reflects_of_preserves _ B.inclusion
  let : PreservesLimitsOfShape WalkingParallelPair
      (SmallProetale.inclusion B S hS ⋙ Over.forget (⟨S, hS⟩ : B.Scheme)) := hforget
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (Over.forget (⟨S, hS⟩ : B.Scheme))

end AlgebraicGeometry.ProEtale

end
