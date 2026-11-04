module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.Unconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafExists

/-!
# The uniqueness of stable models, for families of curves (towards Stacks 0E97)

`AlgebraicGeometry.uniqueStableModels_of` reduces `AlgebraicGeometry.UniqueStableModels` (Stacks
0E97 read for families of curves over the spectrum of a discrete valuation ring) to two inputs:
the total space of a stable family over a discrete valuation ring is a scheme
(`AlgebraicGeometry.stableFamilyTotalIsScheme_of`, from the relative dualizing sheaf of a
prestable family, Stacks 0E6R) and two stable models of a smooth curve are isomorphic
(`AlgebraicGeometry.existsIsoOfStableModels`). Both are proved, so the uniqueness of stable models
holds for every genus.

## Main results

* `AlgebraicGeometry.uniqueStableModels`: `AlgebraicGeometry.UniqueStableModels B hZ g` for every
  `g`.

## Implementation notes

Nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

public section

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The uniqueness of stable models** (Stacks 0E97, read for families of curves): an isomorphism
of the generic fibres of two stable families of curves of genus `g` over a discrete valuation
ring, the generic fibre being smooth, extends uniquely to an isomorphism of the families. -/
theorem uniqueStableModels (g : ℕ) : UniqueStableModels B hZ g :=
  uniqueStableModels_of
    (stableFamilyTotalIsScheme_of B hZ g CurveFamily.exists_isRelativeDualizingSheaf_of_isPrestable)
    (existsIsoOfStableModels B hZ g)

end AlgebraicGeometry

end
