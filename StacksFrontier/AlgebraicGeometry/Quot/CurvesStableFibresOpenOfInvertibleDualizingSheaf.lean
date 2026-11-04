module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingComplexAmplitude
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableFibresOpenOfAffineDualizingComplex

/-!
# Openness of stable fibres within prestable families, from the invertibility of `ω_{X/S}`

For an at-worst-nodal family of curves `X → S` over an affine base, the relative dualizing complex
`ω^•_{X/S} = a(𝒪_S)` lies in degrees `≤ -1`
(`AlgebraicGeometry.CurveFamily.isLE_affineDualizingComplex`). So of the two inputs of
`AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_affineDualizingComplex` only the
invertibility of `ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6R over affine bases) remains.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_isInvertible_affineDualizingSheaf`.

## Implementation notes

Unregistered step of Stacks 0E74 within prestable families.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

-- The same choice of models as
-- `AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_affineDualizingComplex`.
open scoped Stacks.StandardDerivedModel

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) for stable fibres within prestable families, from the invertibility of the
relative dualizing sheaf over affine bases.** If for every at-worst-nodal family of curves `X → S`
with `S` affine the sheaf `ω_{X/S} = H^{-1}(a(𝒪_S))` is invertible (Stacks 0E6R), then the
prestable families with stable fibres form an open locus within the prestable families. The
other input, `a(𝒪_S) ∈ D^{≤ -1}`, is `AlgebraicGeometry.CurveFamily.isLE_affineDualizingComplex`.
-/
theorem isOpenCurvesLocusWithin_hasStableFibres_of_isInvertible_affineDualizingSheaf
    (hinv : ∀ (G : CurveFamily B hZ) (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
        G.base)), Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom →
      Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ G.total.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ G.total.1 G.total.2).O)).property
        ((DerivedCategory.homologyFunctor
          (Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2) (-1)).obj
            (G.affineDualizingComplex hA).obj)) :
    IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ) :=
  isOpenCurvesLocusWithin_hasStableFibres_of_affineDualizingComplex
    (fun G hA hG => CurveFamily.isLE_affineDualizingComplex G hA hG) hinv

end AlgebraicGeometry

end
