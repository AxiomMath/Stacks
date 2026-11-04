module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts

/-!
# The stack of curves is limit preserving (Stacks 0D55)

**Stacks 0D55**: the stack `Curves ⟶ Sch_fppf` of families of curves is *limit preserving* in the
sense of Artin's Axioms, Definition 07XL — for every directed inverse system of affine schemes of
the site with limit `T`, the canonical comparison `colim Curves_{Tᵢ} ⥤ Curves_T` is an equivalence
of categories. It follows from the embedding of Stacks 0D50, the descent of the bound on relative
dimension (Stacks 0D4K, `AlgebraicGeometry.descendsRelativeDimensionLEOne`) and limit preservation
of the finitely presented, flat and proper families of algebraic spaces (Stacks 0D1I,
`AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory`).

## Main results

* `AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`: **Stacks 0D55**, for
  index categories in the universe `u` of the schemes, with no hypothesis beyond the site and its
  containing `Spec(ℤ)`.

## References

* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0D55.** The stack of families of curves over the big fppf site of `Spec(ℤ)` is limit
preserving in the sense of Artin's Axioms, Definition 07XL: for every inverse system of affine
schemes of the site whose limit of underlying schemes is `T`, the canonical comparison
`colim Curves_{Tᵢ} ⥤ Curves_T` is an equivalence of categories. The index category is taken in
the universe of the schemes. -/
@[stacks 0D55 "at a small index category"]
theorem isLimitPreserving_curvesFiberedCategory_unconditional :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ) :=
  isLimitPreserving_curvesFiberedCategory B hZ (descendsRelativeDimensionLEOne B hZ)
    (isLimitPreserving_cartesianProperFlatFiberedCategory B integerBase hZ)

end AlgebraicGeometry

end
