module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocus
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardEssSurj

/-!
# The Picard situation of a family of curves is the one of its proper flat family

For a family of curves `X ⟶ T`, the Picard situation
`AlgebraicGeometry.CurveFamily.picardSituation` (the morphism from the total space of `X ⟶ T` to
`𝒮_T`) is equal to the Picard situation `AlgebraicGeometry.properFlatPicardSituation` of the
finitely presented, flat and proper family `AlgebraicGeometry.CurveFamily.toCartesianProperFlat`
obtained by forgetting the bound on the relative dimension (the inclusion of Stacks 0D50 on
objects). Hence the identification `AlgebraicGeometry.amplePolarizedEquivalence` of the relatively
ample locus of the Picard stack with the polarized families holds at a family of curves.

## Main definitions

* `AlgebraicGeometry.CurveFamily.amplePolarizedEquivalence`: the equivalence of the relatively
  ample locus of `Picardstack_{X/T}` with the category of polarized families over the proper flat
  family of `X ⟶ T`.

## Main results

* `AlgebraicGeometry.CurveFamily.picardSituation_eq`: the two Picard situations are equal.
* `AlgebraicGeometry.CurveFamily.amplePolarizedFunctor_comp_projection`: that equivalence lies
  over the big fppf site of `Spec(ℤ)`.

## References

* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.CurveFamily

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (X : CurveFamily B hZ)

/-- **The Picard situation of a family of curves is the Picard situation of its finitely
presented, flat and proper family of algebraic spaces**
`AlgebraicGeometry.CurveFamily.toCartesianProperFlat`. -/
theorem picardSituation_eq :
    X.picardSituation = properFlatPicardSituation X.toCartesianProperFlat := rfl

variable (hc : Space.ModulePushforwardCoherence B integerBase hZ)

/-- **The moduli identification at a family of curves.** The relatively ample locus of
`Picardstack_{X/T}` is equivalent to the category of polarized families over the proper flat
family of `X ⟶ T`, that is, to the fibre of `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` over it. -/
def amplePolarizedEquivalence :
    (Space.picardAmple hc X.picardSituation).FullSubcategory ≌
      CostructuredArrow (forgetPolarization B) X.toCartesianProperFlat :=
  _root_.AlgebraicGeometry.amplePolarizedEquivalence X.toCartesianProperFlat hc

/-- **The moduli identification at a family of curves lies over the big fppf site of
`Spec(ℤ)`**: an object `(T, ℒ)` of the ample locus lies over `T`, and so does the polarized
family it is sent to. -/
theorem amplePolarizedFunctor_comp_projection :
    (X.amplePolarizedEquivalence hc).functor ⋙
          CostructuredArrow.proj (forgetPolarization B) X.toCartesianProperFlat ⋙
            forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase hZ =
      (Space.picardAmple hc X.picardSituation).ι ⋙
        (Space.picardCFG hc X.picardSituation).val.p :=
  _root_.AlgebraicGeometry.amplePolarizedFunctor_comp_projection X.toCartesianProperFlat hc

end AlgebraicGeometry.CurveFamily

end
