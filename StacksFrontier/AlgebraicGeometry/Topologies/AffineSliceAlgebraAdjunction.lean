module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The affine slice at an affine object is the opposite of a category of algebras

Let `S` be a scheme and `U` an object of `Over S` whose total space `U.left` is affine, and put
`R = Γ(U.left, 𝒪)`. This file constructs the adjunction

`overAffineAlgΓ U ⊣ overAffineAlgSpec U`,
`overAffineAlgSpec U : (CommAlgCat (ULift R))ᵒᵖ ⥤ Over U`,

with `overAffineAlgSpec U` fully faithful and limit-preserving.

The adjunction is a composite of three pieces: `AlgebraicGeometry.algΓAlgSpecAdjunction` over
`Spec (ULift R)`; the transport, by `CategoryTheory.Over.mapIso`, along the identification of
`U.left` with `Spec (ULift R)` given by `AlgebraicGeometry.Scheme.isoSpec` and the universe-lift
ring isomorphism; and `CategoryTheory.Over.iteratedSliceEquiv`, which identifies the slice of
`Over S` at `U` with the slice of schemes at `U.left`.

## Main definitions

* `AlgebraicGeometry.uliftCommRingCatIso`: the universe lift of a commutative ring, as an
  isomorphism of `CommRingCat`.
* `AlgebraicGeometry.overAffineBaseRing`: the universe-lifted coordinate ring of `U.left`.
* `AlgebraicGeometry.specOverAffineBaseRingIso`: `Spec (ULift Γ(U.left, 𝒪)) ≅ U.left`.
* `AlgebraicGeometry.overAffineAlgSpec` and `AlgebraicGeometry.overAffineAlgΓ`: the two
  functors.

## Main results

* `AlgebraicGeometry.overAffineAlgAdjunction`: **the adjunction.**
* `AlgebraicGeometry.full_overAffineAlgSpec`, `AlgebraicGeometry.faithful_overAffineAlgSpec`
  and `AlgebraicGeometry.preservesLimitsOfSize_overAffineAlgSpec`: the right adjoint is fully
  faithful and preserves limits.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The universe lift of a commutative ring, as an isomorphism of `CommRingCat`. -/
public def uliftCommRingCatIso (R : CommRingCat.{u}) : CommRingCat.of (ULift.{u} R) ≅ R :=
  (ULift.ringEquiv (R := R)).toCommRingCatIso

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- The universe-lifted coordinate ring of the total space of an affine object of `Over S`. -/
public abbrev overAffineBaseRing : CommRingCat.{u} := CommRingCat.of (ULift.{u} Γ(U.left, ⊤))

/-- The spectrum of the universe-lifted coordinate ring of `U.left` is `U.left`. -/
public def specOverAffineBaseRingIso : Spec (overAffineBaseRing U) ≅ U.left :=
  (Scheme.Spec.mapIso (uliftCommRingCatIso Γ(U.left, ⊤)).op).symm ≪≫ U.left.isoSpec.symm

/-- **`Spec` into the slice at an affine object of `Over S`.**  An algebra over the
universe-lifted coordinate ring of `U.left` is sent to its spectrum, regarded as an object over
`U` through `AlgebraicGeometry.specOverAffineBaseRingIso`. -/
public def overAffineAlgSpec : (CommAlgCat.{u} (ULift.{u} Γ(U.left, ⊤)))ᵒᵖ ⥤ Over U :=
  algSpec (overAffineBaseRing U) ⋙ (Over.mapIso (specOverAffineBaseRingIso U)).functor ⋙
    (Over.iteratedSliceEquiv U).inverse

/-- **Global sections out of the slice at an affine object of `Over S`**, as an algebra over
the universe-lifted coordinate ring of `U.left`. -/
public def overAffineAlgΓ : Over U ⥤ (CommAlgCat.{u} (ULift.{u} Γ(U.left, ⊤)))ᵒᵖ :=
  (Over.iteratedSliceEquiv U).functor ⋙ (Over.mapIso (specOverAffineBaseRingIso U)).inverse ⋙
    algΓ (overAffineBaseRing U)

/-- **The adjunction `Γ ⊣ Spec` between the slice at an affine object of `Over S` and the
algebras over its coordinate ring.**  The composite of the slice-of-slice equivalence, the
transport along `AlgebraicGeometry.specOverAffineBaseRingIso`, and
`AlgebraicGeometry.algΓAlgSpecAdjunction`. -/
public def overAffineAlgAdjunction : overAffineAlgΓ U ⊣ overAffineAlgSpec U :=
  ((Over.iteratedSliceEquiv U).toAdjunction.comp
      (Over.mapIso (specOverAffineBaseRingIso U)).symm.toAdjunction).comp
    (algΓAlgSpecAdjunction (overAffineBaseRing U))

/-- `AlgebraicGeometry.overAffineAlgSpec` is full. -/
public instance full_overAffineAlgSpec : (overAffineAlgSpec U).Full :=
  haveI : (algSpec (overAffineBaseRing U)).Full := algSpec.instFull
  inferInstanceAs (Functor.Full (algSpec (overAffineBaseRing U) ⋙
    (Over.mapIso (specOverAffineBaseRingIso U)).functor ⋙ (Over.iteratedSliceEquiv U).inverse))

/-- `AlgebraicGeometry.overAffineAlgSpec` is faithful. -/
public instance faithful_overAffineAlgSpec : (overAffineAlgSpec U).Faithful :=
  haveI : (algSpec (overAffineBaseRing U)).Faithful := algSpec.instFaithful
  inferInstanceAs (Functor.Faithful (algSpec (overAffineBaseRing U) ⋙
    (Over.mapIso (specOverAffineBaseRingIso U)).functor ⋙ (Over.iteratedSliceEquiv U).inverse))

/-- `AlgebraicGeometry.overAffineAlgSpec` preserves limits, being a right adjoint. -/
public instance preservesLimitsOfSize_overAffineAlgSpec :
    PreservesLimitsOfSize.{0, 0} (overAffineAlgSpec U) :=
  (overAffineAlgAdjunction U).rightAdjoint_preservesLimits

end AlgebraicGeometry

end
