module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexIdentities
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetSingleShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBoxKunnethSingle

/-!
# The derived direct image along the factorization through `(X, f⁻¹𝒪_S)`

A morphism of schemes `f : X ⟶ S` factors on ringed spaces as `ι : X ⟶ (X, f⁻¹𝒪_S)` followed by
`π : (X, f⁻¹𝒪_S) ⟶ S`. For any morphism `g` of ringed spaces with `ι ≫ π = g` this file records
the isomorphism `Rg_* ≅ Rι_* ⋙ Rπ_*` of derived direct images. The morphism `g` is a parameter,
together with the equation `ι ≫ π = g`, so that the isomorphism can be specialized to any
spelling of the underlying morphism of `f` and reduced to the composition isomorphism by `subst`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageBaseFactorIso`

## References

* [Stacks, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase inverseImageBaseProjection)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardCompIso
  derivedPushforwardCommShift)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.DerivedTensor.RingedSite (DerivedModules)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The isomorphism `Rg_* ≅ Rι_* ⋙ Rπ_*` of derived direct images, for a morphism `g` of
ringed spaces with `ι ≫ π = g`, where `ι : X ⟶ (X, f⁻¹𝒪_S)` and `π : (X, f⁻¹𝒪_S) ⟶ S`. -/
def inverseImageBaseFactorIso (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g) :
    derivedPushforward g ≅
      derivedPushforward (toInverseImageBase f) ⋙ derivedPushforward (inverseImageBaseProjection f)
          :=
  (derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f) ≪≫
    eqToIso (show derivedPushforward (toInverseImageBase f ≫ inverseImageBaseProjection f) =
      derivedPushforward g by rw [hg])).symm

/-- For `g = ι ≫ π` the factorization isomorphism is the inverse of the composition
isomorphism. -/
@[simp]
theorem inverseImageBaseFactorIso_rfl :
    inverseImageBaseFactorIso f _ rfl =
      (derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f)).symm := by
  simp [inverseImageBaseFactorIso]

end AlgebraicGeometry.Scheme.Hom
