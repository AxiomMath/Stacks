module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory

/-!
# `Coh_{X/Y}` for the canonical category structure: Stacks 08W5 and Stacks 08LP

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB.  This file proves two assertions about
`Coh_{X/Y}` at its canonical category structure:

* **Stacks 08W5**, that the projection `p : Coh_{X/Y} ⟶ (Sch/S)_fppf` is fibred in groupoids;
* **Stacks 08LP**, that the square comparing `Coh_{X'/Y'}` with `Coh_{X/Y}` along a morphism
  `g : Y' ⟶ Y` is 2-cartesian.

The canonical category structure is `AlgebraicGeometry.Space.CoherentSituation.categoryData`,
built from the pseudofunctoriality datum `AlgebraicGeometry.Space.modulePushforwardCoherence` of
the inverse images of Stacks 03LU.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.canonicalBaseChangeSquare`: the square of
  Stacks 08LP at the canonical category structures of the two sides.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.projection_isFiberedInGroupoids`: the projection
  `Coh_{X/Y} ⟶ (Sch/S)_fppf` is fibred in groupoids.
* `AlgebraicGeometry.Space.CoherentSituation.canonicalBaseChangeSquare_isTwoFibreProduct`: the
  base-change square is 2-cartesian.

## Implementation notes

Each result is the corresponding statement for an arbitrary
`AlgebraicGeometry.Space.CoherentCategoryData`, applied with
`AlgebraicGeometry.Space.modulePushforwardCoherence`,
`AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation` and
`AlgebraicGeometry.Space.CoherentSituation.categoryData`.

## References

* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-! ### Stacks 08W5 -/

/-- **Stacks 08W5.**  In the situation of Stacks 08KB the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf`, which sends an object `(T, g, F)` to its test scheme `T`, is
fibred in groupoids.

`Coh_{X/Y}` is the category of Stacks 08KB as constructed in
`AlgebraicGeometry.Space.CoherentSituation.categoryData`: its objects are
`AlgebraicGeometry.Space.CoherentObject` (a test scheme `T` over `Y` and a quasi-coherent
`𝒪_{X_T}`-module of finite presentation, flat over `T`, with support proper over `T`), and its
morphisms are `AlgebraicGeometry.Space.CoherentHom` (a morphism `h` of test schemes and an
isomorphism `(X_h)^*F' ⟶ F`).  The base-change stability the lifting half needs is the proved
`AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation`, so nothing is assumed. -/
@[stacks 08W5 "Coh_{X/Y} with the category structure of Stacks 08KB; no hypotheses"]
theorem projection_isFiberedInGroupoids :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Functor.IsFiberedInGroupoids
      (D.categoryData.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y) :=
  coherentProjection_isFiberedInGroupoids' (modulePushforwardCoherence B S hS) D.categoryData

/-! ### Stacks 08LP -/

variable {Y' : AlgebraicSpaces B S hS}

/-- The square of Stacks 08LP at the canonical category structures: the 2-commutative square

`Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y`

whose top row is the base-change functor, whose two vertical arrows are the projections which
forget the module, and whose bottom row is the morphism induced by `g : Y' ⟶ Y`. -/
def canonicalBaseChangeSquare (g : Y' ⟶ D.Y) :
    @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
      (coherentBasedCategory D.categoryData) (baseBasedCategory (D.baseChange g).Y)
      (baseBasedCategory D.Y) (coherentToBase D.categoryData) (baseBasedMap g) :=
  D.baseChangeSquare' (modulePushforwardCoherence B S hS)
    (modulePullbackStabilityOfFinitePresentation B S hS) g D.categoryData
    (D.baseChange g).categoryData

/-- The square `Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y` is 2-cartesian: `Coh_{X'/Y'}`, with
the base-change functor and the projection forgetting the module, is a 2-fibre product of the
projection `Coh_{X/Y} ⟶ 𝒮_Y` with the morphism `𝒮_{Y'} ⟶ 𝒮_Y`. -/
@[stacks 08LP "the base-change square is 2-cartesian"]
def canonicalBaseChangeSquare_isTwoFibreProduct (g : Y' ⟶ D.Y) :
    Bicategory.IsTwoFibreProduct (D.canonicalBaseChangeSquare g) :=
  D.baseChangeSquare_isTwoFibreProduct' (modulePushforwardCoherence B S hS)
    (modulePullbackStabilityOfFinitePresentation B S hS) g D.categoryData
    (D.baseChange g).categoryData

end CoherentSituation

end AlgebraicGeometry.Space

end
