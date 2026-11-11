module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.NormalizationMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The normalization of an algebraic stack over a presenting chart

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces presenting `𝒳 = [U/R]`, and let `N` be a
normalized groupoid for it in the sense of
`AlgebraicGeometry.Stack.NormalizationGroupoid`, so that `𝒳^ν = [U^ν/R^ν]` and
`ν : 𝒳^ν ⟶ 𝒳` is the 1-morphism of Stacks 046Q induced by `(U^ν, R^ν) ⟶ (U, R)`.

Stacks 0GMJ asserts, besides the existence and the integrality of `ν`, that the fibre product of
`ν` with a smooth morphism from a scheme is the normalization of that scheme.  At the presenting
chart `π : 𝒮_U ⟶ 𝒳` of Stacks 044R that assertion reads

```
𝒮_{U^ν} ----> 𝒳^ν
   |            |  ν
   v            v
  𝒮_U -------> 𝒳
          π
```
is 2-cartesian, and this file proves it: the defining cartesian source square
`R^ν = R ×_{s, U} U^ν` of the normalized groupoid is exactly the hypothesis of Stacks 04ZN, which
this library proves as
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_normalizationChartSquare`: the square above is a
  2-fibre product of stacks in groupoids over the big fppf site; equivalently
  `𝒳^ν ×_𝒳 𝒮_U = 𝒮_{U^ν}`.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_normalizationChartSquare_swap`: the same square read
  over the reversed cospan, which is the order in which the chart is the first leg.
* `AlgebraicGeometry.Stack.objectsMap_hom_eq_normalizationData_hom`: the leg
  `𝒮_{U^ν} ⟶ 𝒮_U` of that square is induced by the normalization morphism `U^ν ⟶ U` of the
  object space, so the identification is the one Stacks 0GMJ states.

## Implementation notes

**What the statement does and does not assume.**  The only input is the normalized groupoid `N`,
which is the object the source's proof constructs out of Stacks 07U4 and which
`StacksFrontier.AlgebraicGeometry.Stacks.NormalizationMorphism` carries as data for the reason
recorded there.  Nothing else is hypothesised: the cartesian source square is a field of `N`, and
Stacks 04ZN is proved in this library.  In particular neither the representability of `ν`
(Stacks 04ZP) nor Stacks 04TK is needed to state or to prove the identification, since a 2-fibre
product of stacks in groupoids is terminality in the category of 2-commutative squares of
Stacks 003O and makes no reference to either.

**Which 2-category.**  The square lives in the 2-category of stacks in groupoids of Stacks 02ZK,
because that is where Stacks 04ZN is proved; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquare` for why a square proved
2-cartesian there cannot be moved to the 2-category of categories fibred in groupoids of
Stacks 02XS, which is where
`AlgebraicGeometry.Stack.isIntegralHom_quotientStackMapHom_normalization` performs its descent.
So this file supplies the fibre-product assertion of Stacks 0GMJ at the presenting chart, and the
hypotheses of that other declaration are untouched by it.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- **Stacks 0GMJ, the fibre-product assertion at the presenting chart.**  For a groupoid in
algebraic spaces `(U, R, s, t, c)` presenting `𝒳 = [U/R]` and a normalized groupoid `N` for it,
the square formed by the normalization 1-morphism `ν : [U^ν/R^ν] ⟶ [U/R]` of Stacks 046Q and the
canonical projection `𝒮_U ⟶ [U/R]` of Stacks 044R is a 2-fibre product with apex `𝒮_{U^ν}`; that
is, `𝒳^ν ×_𝒳 U = U^ν`.

This is the assertion of Stacks 0GMJ that the source obtains from `R^ν = R ×_{s, U} U^ν` by
citing Stacks 04ZN, and the proof here is that citation: the cartesian source square is the field
`AlgebraicGeometry.Stack.NormalizationGroupoid.isPullback_source` of the normalized groupoid, and
Stacks 04ZN is
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`.

This is one step of the proof of Stacks 0GMJ, at the presenting chart only and with the
normalized groupoid as data; Stacks 0GMJ, for every smooth morphism from a scheme, is
`AlgebraicStacks.isIntegralHom_normalization_and_isTwoFibreProduct_normSpace`. -/
noncomputable def isTwoFibreProduct_normalizationChartSquare
    (N : NormalizationGroupoid C S hS G) :
    Bicategory.IsTwoFibreProduct (functorialitySquare N.hom) :=
  isTwoFibreProduct_functorialitySquare_of_isPullback N.hom N.isPullback_source

/-- The square of `AlgebraicGeometry.Stack.isTwoFibreProduct_normalizationChartSquare` read over
the reversed cospan, so that the presenting chart `𝒮_U ⟶ [U/R]` is its first leg and the
normalization `ν` its second. -/
noncomputable def isTwoFibreProduct_normalizationChartSquare_swap
    (N : NormalizationGroupoid C S hS G) :
    Bicategory.IsTwoFibreProduct (functorialitySquare N.hom).swap :=
  Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_normalizationChartSquare N)

/-- The morphism of object spaces underlying the normalization morphism of groupoids is the
normalization morphism `U^ν ⟶ U` of the object space, read through the identification of the
object space of the normalized groupoid with the normalization of `U`.

The leg `𝒮_{U^ν} ⟶ 𝒮_U` of the 2-fibre product square is the one this morphism induces, which is
what makes the identification of
`AlgebraicGeometry.Stack.isTwoFibreProduct_normalizationChartSquare` the assertion of
Stacks 0GMJ rather than a statement about an unnamed morphism. -/
theorem objectsMap_hom_eq_normalizationData_hom (N : NormalizationGroupoid C S hS G) :
    N.hom.objectsMap.hom = eqToHom N.objects_eq ≫ N.data.hom :=
  N.mapObjects_eq

end AlgebraicGeometry.Stack

end
