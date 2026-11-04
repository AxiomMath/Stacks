module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingComplexFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableFibresOpenOfDualizing
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Stable fibres within prestable families, from the relative dualizing complex

`AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf_of_isAffine` derives
condition (o) for stable fibres within prestable families (the openness half of Stacks 0E74) from
the relative dualizing sheaf `ω_{X/S}` of at-worst-nodal families over affine bases: an invertible
module whose pullback to every fibre is the dualizing sheaf of the fibre. This file supplies the
fibre identification for `ω_{X/S} = H^{-1}(ω^•_{X/S})`, `ω^•_{X/S} = a(𝒪_S)` the relative dualizing
complex over the affine base (Section 0E6N, Definition 0E6Q), so that the remaining inputs are the
two halves of Stacks 0E6P/0E6R for at-worst-nodal families over affine bases: `ω^•_{X/S}` has no
cohomology above degree `-1`, and `H^{-1}(ω^•_{X/S})` is invertible.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocusWithin_hasStableFibres_of_affineDualizingComplex`.

## Implementation notes

Unregistered helper for Stacks 0E74. The inputs `hle` and `hinv` are written out as
the statements they are (no stand-in predicates).

## References

* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

-- The relative dualizing complex lives at the standard model of the derived category; among the
-- imports here a global instance (`ChaoticComparison.sheafOfModules_hasDerivedCategory`) also
-- applies to modules on small étale sites, so the standard model is selected by its scope.
open scoped Stacks.StandardDerivedModel

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) for stable fibres within prestable families, from the relative dualizing
complex over affine bases.** For an at-worst-nodal family of curves `X → S` with `S` affine let
`ω^•_{X/S} = a(𝒪_S)` (`AlgebraicGeometry.CurveFamily.affineDualizingComplex`). If `ω^•_{X/S}` has
no cohomology above degree `-1` (`hle`) and `ω_{X/S} = H^{-1}(ω^•_{X/S})` is invertible (`hinv`)
— the two halves of Stacks 0E6P and 0E6R over affine bases — then the prestable families with
stable fibres form an open locus within the prestable families. -/
theorem isOpenCurvesLocusWithin_hasStableFibres_of_affineDualizingComplex
    (hle : ∀ (G : CurveFamily B hZ) (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
        G.base)), Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom →
      (G.affineDualizingComplex hA).obj.IsLE (-1))
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
  isOpenCurvesLocusWithin_hasStableFibres_of_dualizingSheaf_of_isAffine fun G hA hG =>
    ⟨_, hinv G hA hG, fun p V v q _ h =>
      CurveFamily.nonempty_baseChangeModule_homology_affineDualizingComplex_iso G hA
        (hle G hA hG) p V v q h⟩

end AlgebraicGeometry

end
