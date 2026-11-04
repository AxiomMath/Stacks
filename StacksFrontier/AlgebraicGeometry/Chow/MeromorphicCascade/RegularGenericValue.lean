module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.GenericValue
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionRatio

/-!
# The generic value of a regular meromorphic section is nonzero

Let `X` be an integral scheme and let `F` be a quasi-coherent `𝒪_X`-module. A meromorphic section
of `F` is a global section of the sheaf `𝒦_X(F)` of [Stacks, Tag 01X4], and
`Stacks.Divisors.genericValue` reads it as an element of the generic stalk `F_η` through the
comparison of [Stacks, Tag 01X5] part (2). This file records that a *regular* section has nonzero
generic value, which is the hypothesis the choice-independence of [Stacks, Tag 02SJ] part (2) is
stated under.

`AlgebraicGeometry.val_top_ne_zero_of_isRegularMeromorphicSection` already proves that a regular
meromorphic section is nonzero as a section over the whole space; the comparison of Tag 01X5
part (2) is an additive equivalence, so the generic value is nonzero too.

## Main results

* `Stacks.Divisors.genericValue_ne_zero_of_isRegularMeromorphicSection` — the generic value of a
  regular meromorphic section is nonzero.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

/-- On an integral scheme, the generic value of a regular meromorphic section of a quasi-coherent
module is nonzero. -/
theorem genericValue_ne_zero_of_isRegularMeromorphicSection {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf F)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf F s) :
    genericValue F s ≠ 0 := fun h ↦
  AlgebraicGeometry.val_top_ne_zero_of_isRegularMeromorphicSection F s hs <|
    (meromorphicSectionsAddEquivGenericStalk F ⊤ trivial).injective (h.trans (map_zero _).symm)

end Stacks.Divisors

end
