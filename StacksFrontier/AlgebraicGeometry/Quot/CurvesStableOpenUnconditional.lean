module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenOfDualizing
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Open
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafExists
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional

/-!
# The open substacks `𝓜̄` and `𝓜̄_g` of the stack of curves (towards Stacks 0E76, 0E78)

`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_dualizing` cuts out
`𝓜̄ = Curves^{stable}` in `Curves` from condition (o) for `Curves^{h0,1}` (Stacks 0E6I) and the
existence of a relative dualizing sheaf on every prestable family (Stacks 0E6P, 0E6Q, 0E6R). Both
are now proved (`AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily` and
`AlgebraicGeometry.CurveFamily.exists_isRelativeDualizingSheaf_of_isPrestable`), so the openness
of `𝓜̄` holds with no hypothesis. The openness of `𝓜̄_g` and of `𝓜_g` (smooth, `f_*𝒪_X = 𝒪_S`
universally, of genus `g`) are reduced to parts (2) and (3) of Stacks 0E1J.

## Main results

* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`: condition (o) of
  Stacks 0E0E for `𝓜̄` (the openness of Stacks 0E76).
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3`: condition (o) for
  `𝓜̄_g` (the openness part of Stacks 0E78), from parts (2) and (3) of Stacks 0E1J.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3`: condition (o) for
  `𝓜_g` (Stacks 0E83), from parts (2) and (3) of Stacks 0E1J.

## Implementation notes

Nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

public section

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Condition (o) for `𝓜̄_g`** (the openness part of Stacks 0E78), from parts (2) (`h2`) and
(3) (`h3`) of Stacks 0E1J. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 (g : ℕ)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_dualizing B hZ g
    isOpenCurvesLocus_isH01CurveFamily
    CurveFamily.exists_isRelativeDualizingSheaf_of_isPrestable h2 h3

/-- **Condition (o) for `𝓜_g`** (Stacks 0E83): smooth families with `f_*𝒪_X = 𝒪_S` universally
and `R¹f_*𝒪_X` locally free of rank `g`, from parts (2) (`h2`) and (3) (`h3`) of Stacks 0E1J. -/
theorem isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 (g : ℕ)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g) :=
  isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_isH01 B hZ g
    isOpenCurvesLocus_isH01CurveFamily h2 h3

end AlgebraicGeometry

end
