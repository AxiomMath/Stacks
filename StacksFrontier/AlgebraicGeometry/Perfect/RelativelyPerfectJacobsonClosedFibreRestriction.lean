module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# The closed fibre of Stacks 0DJZ over an affine chart

Let `(R, I)` be a ring with an ideal, write `S = Spec R` and `S₀ = Spec (R/I)`, let
`f : X ⟶ S` be a morphism of schemes and put `X₀ = S₀ ×_S X`. The derived restriction of an
object `E` of `D(𝒪_X)` to the closed fibre is its derived pullback along
`AlgebraicGeometry.Scheme.Hom.closedFibreToTotal`, the projection `X₀ ⟶ X`.

The source's proof of Stacks 0DJZ reads that derived restriction over an affine open `U` of `X`,
where it becomes a ring-level derived base change. This file takes the first of the two steps
needed: it restricts the derived pullback to the chart, over the preimage of `U` in `X₀`, and
records that the preimage is again an affine open, the projection being an affine morphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_closedFibreToTotal`: the preimage in `X₀` of
  an affine open of `X` is affine.
* `AlgebraicGeometry.Scheme.Hom.restrictDerivedPullbackClosedFibreToTotalIso`: the restriction to
  that preimage of the derived restriction of `E` to the closed fibre is the derived pullback of
  `E|_U` along the restricted projection.

## What this does not do

The second step is the identification of the restricted projection with the morphism of affine
schemes attached to the ring map `Γ(X, U) ⟶ Γ(X, U) ⧸ I·Γ(X, U)`, and of the derived pullback
along it with `K ↦ (Γ(X, U) ⧸ I·Γ(X, U)) ⊗^𝐋_{Γ(X, U)} K` by
`AlgebraicGeometry.StandardModel.affinePullbackComparison`. Neither is proved here. What is needed
for it is the computation of `S₀ ×_S U` as the spectrum of `R/I ⊗_R Γ(X, U)`, and the transport of
`affinePullbackComparison` along `AlgebraicGeometry.IsAffineOpen.isoSpec` on both sides.

## Implementation notes

The commuting square of open immersions is discharged by
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` and the transport by
`AlgebraicGeometry.Scheme.Modules.openRestrictionDerivedPullbackIso`, which asks for no flatness —
the projection from the closed fibre is not flat. A `private` instance of the same transport, for a
general morphism and a general pair of opens, is used inside the proof of Stacks 09US in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US`.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.10.2 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- **The projection from the closed fibre is an affine morphism.** It is the base change of the
closed immersion `Spec (R/I) ⟶ Spec R` along `f`, and affineness of a morphism is stable under
base change. -/
public instance isAffineHom_closedFibreToTotal : IsAffineHom (closedFibreToTotal f I) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback (closedBase I) f) inferInstance

/-- **The preimage in the closed fibre of an affine open is affine.** An affine morphism pulls
affine opens back to affine opens, and `closedFibreToTotal` is affine. -/
public theorem isAffineOpen_preimage_closedFibreToTotal {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (closedFibreToTotal f I ⁻¹ᵁ U) :=
  IsAffineHom.isAffine_preimage (f := closedFibreToTotal f I) U hU

/-- **The derived restriction to the closed fibre, read over a chart.** For an open `U` of `X`,
restricting to its preimage in `X₀` the derived restriction of `E` to the closed fibre gives the
derived pullback of `E|_U` along the restriction of the projection.

This is `AlgebraicGeometry.Scheme.Modules.openRestrictionDerivedPullbackIso` at the square equating
`(closedFibreToTotal f I ⁻¹ᵁ U).ι ≫ closedFibreToTotal f I` and
`(closedFibreToTotal f I).resLE U _ ≫ U.ι`. No flatness is used, and none is available: the
projection from the closed fibre is a base change of a closed immersion. -/
public def restrictDerivedPullbackClosedFibreToTotalIso (U : X.Opens)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (Scheme.Modules.restrictFunctor (closedFibreToTotal f I ⁻¹ᵁ U).ι).mapDerivedCategory.obj
        ((derivedPullback (closedFibreToTotal f I).toLRSHom.toShHom).obj E) ≅
      (derivedPullback
          ((closedFibreToTotal f I).resLE U (closedFibreToTotal f I ⁻¹ᵁ U)
            le_rfl).toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) :=
  Scheme.Modules.openRestrictionDerivedPullbackIso (closedFibreToTotal f I ⁻¹ᵁ U).ι
    (closedFibreToTotal f I) U.ι
    ((closedFibreToTotal f I).resLE U (closedFibreToTotal f I ⁻¹ᵁ U) le_rfl)
    (Scheme.Hom.resLE_comp_ι (closedFibreToTotal f I) le_rfl).symm E

end AlgebraicGeometry.Scheme.Hom

end
