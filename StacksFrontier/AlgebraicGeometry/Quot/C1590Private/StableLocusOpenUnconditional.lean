module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafNodal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniversallyBijectiveGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen

/-!
# The stable locus of the stack of curves is open (Stacks 0E76)

`AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily_of` proves condition (o) of
Stacks 0E0E for stable families of curves from three inputs, supplied here:

* condition (o) for prestable families (Stacks 0E6U), from condition (o) for `Curves^{h0,1}`
  (Stacks 0E6I) through `AlgebraicGeometry.isOpenCurvesLocus_isPrestableCurveFamily_of`, whose
  inputs are Stacks 0E0R at `i = 0`
  (`AlgebraicGeometry.C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of`)
  and Stacks 0E6B (a) (`AlgebraicGeometry.C1590Private.hasUniversallyBijectiveGlobalFunctions_of`);
* the étale local scheme charts of a family of curves (Stacks 0E6F,
  `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`);
* the relative dualizing sheaf of a nodal family of schemes over an affine base (Stacks 0E6R,
  `AlgebraicGeometry.C1590Private.hasNodalRelativeDualizingSheaf`).

## Main results

* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`: condition (o) for
  `Curves^{stable}`, the openness assertion of Stacks 0E76.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The openness of `Curves^{stable}` (Stacks 0E76)**, as condition (o) of Stacks 0E0E: every
family of curves has a largest open of its base over which it is stable, and its formation
commutes with arbitrary base change. -/
theorem isOpenCurvesLocus_isStableCurveFamily :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) :=
  isOpenCurvesLocus_isStableCurveFamily_of
    (isOpenCurvesLocus_isPrestableCurveFamily_of
      (isOpenCurvesLocus_isH01CurveFamily_of
        (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
          (hasEtaleLocalSchemeCharts B hZ))
        (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))))
    (hasEtaleLocalSchemeCharts B hZ) hasNodalRelativeDualizingSheaf

end AlgebraicGeometry.C1590Private

end
