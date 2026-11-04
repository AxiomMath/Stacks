module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.ULiftHom
import all StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves

/-!
# The stack of polarized curves is an open and closed substack of `𝒫olarized` (Stacks 0DPZ)

The stack `𝒫olarized` of polarized proper schemes, as a category fibred in groupoids over the big
fppf site of `Spec(ℤ)` with morphisms at the raised universe, with no hypothesis; the 2-fibre
product square defining *PolarizedCurves* over it (Stacks 0DPY); and Stacks 0DPZ: the projection
`PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces, an open immersion and a
closed immersion.

## Main definitions

* `AlgebraicGeometry.polarizedFiberedCategoryUnconditional`: the stack `𝒫olarized`.
* `AlgebraicGeometry.polarizedToCartesianProperFlatHomUnconditional`: forgetting the
  polarization, `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}`.
* `AlgebraicGeometry.polarizedCurvesSquareUnconditionalUp`: the 2-fibre product square defining
  *PolarizedCurves*.
* `AlgebraicGeometry.polarizedCurvesFiberedCategoryUnconditional`: *PolarizedCurves*.
* `AlgebraicGeometry.polarizedCurvesToPolarizedUnconditionalUp`: the projection
  `PolarizedCurves ⟶ 𝒫olarized`.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized_unconditional`:
  the projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces.
* `AlgebraicGeometry.isOpenImmersion_polarizedCurvesToPolarized_unconditional`: it is an open
  immersion.
* `AlgebraicGeometry.isClosedImmersion_polarizedCurvesToPolarized_unconditional`: it is a closed
  immersion.

## References

* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
* [Stacks Project, Tag 0DPY](https://stacks.math.columbia.edu/tag/0DPY)
* [Stacks Project, Tag 0DPZ](https://stacks.math.columbia.edu/tag/0DPZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The category of polarized families at a raised morphism universe -/

/-- `AlgebraicGeometry.integerBase` is terminal in the big fppf site, with the unique morphism
out of an object given by the terminal morphism of schemes. With this unique morphism,
`AlgebraicGeometry.schemeOverIntegers` is definitionally the reindexing
`CategoryTheory.Functor.sliceAtTerminal` along it. -/
def isTerminal_obj_integerBase : Limits.IsTerminal (B.obj hZ) :=
  Limits.IsTerminal.ofUniqueHom (fun X ↦ ObjectProperty.homMk (specULiftZIsTerminal.from X.obj))
    fun _ _ ↦ by
      apply ObjectProperty.hom_ext
      exact specULiftZIsTerminal.hom_ext _ _

/-- The second assertion of Stacks 0D3Z at the raised morphism universe: polarized families are
fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
theorem isFiberedInGroupoids_polarizedProjectionOver_unconditional :
    (polarizedProjectionOver B hZ).IsFiberedInGroupoids :=
  (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B).uliftHomDown

/-- The stack `𝒫olarized` of polarized proper schemes (Stacks 0D1M) as an object of the
2-category of categories fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
def polarizedFiberedCategoryUnconditional :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (polarizedProjectionOver B hZ))
    (isFiberedInGroupoids_polarizedProjectionOver_unconditional B hZ)

/-- Forgetting the polarization (Stacks 0D3Y), as a 1-morphism of categories fibred in groupoids
over the big fppf site of `Spec(ℤ)`. -/
def polarizedToCartesianProperFlatHomUnconditional :
    polarizedFiberedCategoryUnconditional B hZ ⟶
      cartesianProperFlatFiberedCategory B integerBase hZ :=
  Bicategory.InducedBicategory.mkHom
    ({ toFunctor := forgetPolarizationUp B hZ, w := forgetPolarizationUp_comp B hZ })

/-! ### The stack of polarized curves -/

/-- The 2-fibre product square defining the stack of polarized curves (Stacks 0DPY): the cospan
is the forgetful 1-morphism of Stacks 0D3Y and the inclusion of Stacks 0D50, and the apex is the
canonical 2-fibre product of Stacks 0040. -/
def polarizedCurvesSquareUnconditionalUp :
    Bicategory.TwoCommSq (polarizedToCartesianProperFlatHomUnconditional B hZ)
      (curvesToCartesianProperFlatHom B hZ) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _

/-- *PolarizedCurves*, the 2-fibre product `𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`: a
family of curves together with a relatively ample invertible module on its total space. -/
def polarizedCurvesFiberedCategoryUnconditional :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  (polarizedCurvesSquareUnconditionalUp B hZ).pt

/-- The projection `PolarizedCurves ⟶ 𝒫olarized`, which forgets the bound on the relative
dimension of the family. -/
def polarizedCurvesToPolarizedUnconditionalUp :
    polarizedCurvesFiberedCategoryUnconditional B hZ ⟶
      polarizedFiberedCategoryUnconditional B hZ :=
  (polarizedCurvesSquareUnconditionalUp B hZ).fst

/-- The square of `AlgebraicGeometry.polarizedCurvesSquareUnconditionalUp` is a 2-fibre product,
being the canonical one. Being a 2-fibre product is terminality in the category of 2-commutative
squares over the cospan, so this is data rather than a proposition. -/
def isTwoFibreProduct_polarizedCurvesSquareUnconditionalUp :
    Bicategory.IsTwoFibreProduct (polarizedCurvesSquareUnconditionalUp B hZ) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _

/-! ### Stacks 0DPZ -/

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces. -/
@[stacks 0DPZ "representability by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized_unconditional :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (polarizedCurvesToPolarizedUnconditionalUp B hZ).hom :=
  Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategoryUnconditional B hZ) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHomUnconditional B hZ)
    (polarizedCurvesSquareUnconditionalUp B hZ)
    (isTwoFibreProduct_polarizedCurvesSquareUnconditionalUp B hZ)
    (isRepresentableByAlgebraicSpaces_curvesToCartesianProperFlat B hZ)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is an open immersion. -/
@[stacks 0DPZ "open immersion"]
theorem isOpenImmersion_polarizedCurvesToPolarized_unconditional :
    Stack.IsOpenImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditionalUp B hZ) :=
  Stack.isOpenImmersion_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategoryUnconditional B hZ) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHomUnconditional B hZ)
    (polarizedCurvesSquareUnconditionalUp B hZ)
    (isTwoFibreProduct_polarizedCurvesSquareUnconditionalUp B hZ)
    (isOpenImmersion_curvesToCartesianProperFlat B hZ)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is a closed immersion. -/
@[stacks 0DPZ "closed immersion"]
theorem isClosedImmersion_polarizedCurvesToPolarized_unconditional :
    Stack.IsClosedImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditionalUp B hZ) :=
  Stack.isClosedImmersion_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategoryUnconditional B hZ) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHomUnconditional B hZ)
    (polarizedCurvesSquareUnconditionalUp B hZ)
    (isTwoFibreProduct_polarizedCurvesSquareUnconditionalUp B hZ)
    (isClosedImmersion_curvesToCartesianProperFlat B hZ)

end AlgebraicGeometry

end
