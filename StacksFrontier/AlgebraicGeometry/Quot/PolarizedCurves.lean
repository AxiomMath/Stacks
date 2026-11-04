module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.ULiftHom

/-!
# The stack of polarized curves (Stacks 0DPY, 0DPZ)

Stacks 0DPY defines *PolarizedCurves* as the 2-fibre product
`𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`: an object is a family of curves together with
a relatively ample invertible module on its total space. Stacks 0DPZ says that the projection
`PolarizedCurves ⟶ 𝒫olarized` is an open and closed immersion, and the whole of its proof is
that the other leg of the cospan, the inclusion `𝒞urves ⟶ 𝒮paces'_{fp, flat, proper}` of
Stacks 0D50, is representable by open and closed immersions, which is Stacks 0D5B. The
projection is its base change, and representability, the open-immersion property and the
closed-immersion property are all stable under base change by Stacks 0302 and Stacks 045C.

## The hypothesis this file carries

The cospan needs `𝒫olarized` as an object of the 2-category of categories fibred in groupoids
over the big fppf site of `AlgebraicGeometry.integerBase`, so it needs the second assertion of
**Stacks 0D3Z** — that the category `AlgebraicGeometry.PolarizedFamily` of Stacks 0D1M is fibred
in groupoids over the big fppf site — which this library does not yet have. Every result below
therefore takes it as the explicit hypothesis
`(polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids`,
and nothing else about the polarized side is assumed: the functor
`AlgebraicGeometry.forgetPolarization` of **Stacks 0D3Y** is the one the library already has, and
the 2-fibre product is the canonical one of Stacks 0040. Once Stacks 0D3Z is formalized the
hypothesis is discharged by it and these statements become unconditional.

## Main definitions

* `AlgebraicGeometry.PolarizedFamilyUp` and `AlgebraicGeometry.polarizedProjectionOver`: the
  category of polarized families presented over the big fppf site of `Spec(ℤ)` at the morphism
  universe the 2-category of Stacks 02XS uses here.
* `AlgebraicGeometry.polarizedFiberedCategory` and
  `AlgebraicGeometry.polarizedToCartesianProperFlatHom`: `𝒫olarized` as an object of that
  2-category, and the forgetful 1-morphism (Stacks 0D3Y) to
  `AlgebraicGeometry.cartesianProperFlatFiberedCategory`.
* `AlgebraicGeometry.polarizedCurvesSquare`, `AlgebraicGeometry.polarizedCurvesFiberedCategory`
  and `AlgebraicGeometry.polarizedCurvesToPolarized`: **Stacks 0DPY**, the 2-fibre product
  square, its apex *PolarizedCurves*, and the projection to `𝒫olarized`.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized`,
  `AlgebraicGeometry.isOpenImmersion_polarizedCurvesToPolarized` and
  `AlgebraicGeometry.isClosedImmersion_polarizedCurvesToPolarized`: **Stacks 0DPZ**, the
  projection `PolarizedCurves ⟶ 𝒫olarized` is an open and closed immersion.

## Implementation notes

The three conclusions are the ones Stacks 04YL asks for of a 1-morphism that is an open,
respectively closed, immersion: representability by algebraic spaces together with the Stacks
04XB property at the open-, respectively closed-immersion property of morphisms of algebraic
spaces. They are split over three declarations for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered` for Stacks 0D5B, whose three
declarations they are the base changes of. As there, nothing is asked of either side beyond
being fibred in groupoids, so the conclusions are the predicates
`AlgebraicGeometry.Stack.IsOpenImmersion` and `AlgebraicGeometry.Stack.IsClosedImmersion` rather
than `AlgebraicGeometry.Stack.AlgebraicStacks.IsOpenImmersion` and its companion, which would
need `𝒫olarized` and *PolarizedCurves* to be known to be algebraic stacks (Stacks 0D4X).

`AlgebraicGeometry.PolarizedFamily` has its morphisms in `Type u`, while the morphisms of
`AlgebraicGeometry.CurveFamily` and of `AlgebraicGeometry.CartesianProperFlatSpaces` are natural
transformations of presheaves on the big fppf site and so lie in `Type (u + 1)`. A cospan inside
the 2-category of Stacks 02XS has one morphism universe for all three of its categories, so the
polarized side is repackaged by `CategoryTheory.ULiftHom`, which keeps the objects and wraps the
morphisms; `CategoryTheory.Functor.IsFiberedInGroupoids.uliftHomDown` carries Stacks 003S across
the repackaging, so the hypothesis is still stated for the structure functor of
`AlgebraicGeometry.PolarizedFamily` itself. That `AlgebraicGeometry.forgetPolarization` is a
functor over the site — the equality `AlgebraicGeometry.forgetPolarizationUp_comp` that makes it
a 1-morphism of the 2-category — holds by `rfl`, which is the content of
`AlgebraicGeometry.forgetPolarization_obj_base` and
`AlgebraicGeometry.forgetPolarization_map_base`.

The universes are those of Stacks 0302 and Stacks 045C as formalized, namely
`CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`, which is where the three categories of the
cospan live.

## References

* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
* [Stacks Project, Tag 0DPY](https://stacks.math.columbia.edu/tag/0DPY)
* [Stacks Project, Tag 0DPZ](https://stacks.math.columbia.edu/tag/0DPZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The category of polarized families at a raised morphism universe -/

/-- The category `AlgebraicGeometry.PolarizedFamily` of polarized families (Stacks 0D1M) with
its morphisms wrapped in `ULift`, so that it sits in the same 2-category of categories fibred in
groupoids as the category of families of curves and the category of finitely presented, flat and
proper families of algebraic spaces. The objects are unchanged. -/
abbrev PolarizedFamilyUp := ULiftHom.{u + 1} (PolarizedFamily B)

/-- The projection taking a polarized family to its base scheme, read as a scheme over
`AlgebraicGeometry.integerBase`: this is how the category of polarized families is a category
over the big fppf site of `Spec(ℤ)`. -/
def polarizedProjectionOver : PolarizedFamilyUp B ⥤ BigFppfOver B integerBase hZ :=
  (ULiftHom.down : PolarizedFamilyUp B ⥤ PolarizedFamily B) ⋙
    polarizedProjection B ⋙ schemeOverIntegers B

/-- **Stacks 0D3Y.** The forgetful functor of `AlgebraicGeometry.forgetPolarization`, read on the
repackaged category of polarized families. -/
def forgetPolarizationUp : PolarizedFamilyUp B ⥤ CartesianProperFlatSpaces B integerBase hZ :=
  (ULiftHom.down : PolarizedFamilyUp B ⥤ PolarizedFamily B) ⋙ forgetPolarization B

/-- **Stacks 0D3Y.** Forgetting the polarization keeps the base scheme, so the forgetful functor
is a functor over the big fppf site of `Spec(ℤ)`. -/
theorem forgetPolarizationUp_comp :
    forgetPolarizationUp B hZ ⋙ cartesianProperFlatProjection B integerBase hZ =
      polarizedProjectionOver B hZ :=
  rfl

/-- The second assertion of Stacks 0D3Z, transported to the repackaged category: if the category
of polarized families is fibred in groupoids over the big fppf site of `Spec(ℤ)`, then so is its
repackaging at the raised morphism universe. -/
theorem isFiberedInGroupoids_polarizedProjectionOver
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    (polarizedProjectionOver B hZ).IsFiberedInGroupoids :=
  h3Z.uliftHomDown

/-- The stack `𝒫olarized` of polarized proper schemes (Stacks 0D1M) as an object of the
2-category of categories fibred in groupoids over the big fppf site of `Spec(ℤ)`, given the
second assertion of Stacks 0D3Z. -/
def polarizedFiberedCategory
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (polarizedProjectionOver B hZ))
    (isFiberedInGroupoids_polarizedProjectionOver B hZ h3Z)

/-- **Stacks 0D3Y.** Forgetting the polarization, as a 1-morphism of categories fibred in
groupoids over the big fppf site of `Spec(ℤ)`. -/
def polarizedToCartesianProperFlatHom
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    polarizedFiberedCategory B hZ h3Z ⟶ cartesianProperFlatFiberedCategory B integerBase hZ :=
  Bicategory.InducedBicategory.mkHom
    ({ toFunctor := forgetPolarizationUp B hZ, w := forgetPolarizationUp_comp B hZ })

/-! ### The stack of polarized curves -/

/-- **Stacks 0DPY.** The 2-fibre product square defining the stack of polarized curves: the
cospan is the forgetful 1-morphism of Stacks 0D3Y and the inclusion of Stacks 0D50, and the apex
is the canonical 2-fibre product of Stacks 0040. -/
def polarizedCurvesSquare
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    Bicategory.TwoCommSq (polarizedToCartesianProperFlatHom B hZ h3Z)
      (curvesToCartesianProperFlatHom B hZ) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _

/-- **Stacks 0DPY.** *PolarizedCurves*, the 2-fibre product
`𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`: a family of curves together with a relatively
ample invertible module on its total space. -/
def polarizedCurvesFiberedCategory
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  (polarizedCurvesSquare B hZ h3Z).pt

/-- **Stacks 0DPY.** The projection `PolarizedCurves ⟶ 𝒫olarized`, which forgets the bound on
the relative dimension of the family. -/
def polarizedCurvesToPolarized
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    polarizedCurvesFiberedCategory B hZ h3Z ⟶ polarizedFiberedCategory B hZ h3Z :=
  (polarizedCurvesSquare B hZ h3Z).fst

/-- The square of `AlgebraicGeometry.polarizedCurvesSquare` is a 2-fibre product, being the
canonical one. Being a 2-fibre product is terminality in the category of 2-commutative squares
over the cospan, so this is data rather than a proposition. -/
def isTwoFibreProduct_polarizedCurvesSquare
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    Bicategory.IsTwoFibreProduct (polarizedCurvesSquare B hZ h3Z) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _

/-! ### Stacks 0DPZ -/

/-- **Stacks 0DPZ.** The projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic
spaces, being the base change of the inclusion of Stacks 0D50, which is representable by
algebraic spaces by Stacks 0D5B. -/
@[stacks 0DPZ "representability by algebraic spaces, given Stacks 0D3Z"]
theorem isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (polarizedCurvesToPolarized B hZ h3Z).hom :=
  Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategory B hZ h3Z) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHom B hZ h3Z) (polarizedCurvesSquare B hZ h3Z)
    (isTwoFibreProduct_polarizedCurvesSquare B hZ h3Z)
    (isRepresentableByAlgebraicSpaces_curvesToCartesianProperFlat B hZ)

/-- **Stacks 0DPZ.** The projection `PolarizedCurves ⟶ 𝒫olarized` is an open immersion, being
the base change of the inclusion of Stacks 0D50, which is an open immersion by Stacks 0D5B. -/
@[stacks 0DPZ "open immersion, given Stacks 0D3Z"]
theorem isOpenImmersion_polarizedCurvesToPolarized
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    Stack.IsOpenImmersion B integerBase hZ (polarizedCurvesToPolarized B hZ h3Z) :=
  Stack.isOpenImmersion_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategory B hZ h3Z) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHom B hZ h3Z) (polarizedCurvesSquare B hZ h3Z)
    (isTwoFibreProduct_polarizedCurvesSquare B hZ h3Z)
    (isOpenImmersion_curvesToCartesianProperFlat B hZ)

/-- **Stacks 0DPZ.** The projection `PolarizedCurves ⟶ 𝒫olarized` is a closed immersion, being
the base change of the inclusion of Stacks 0D50, which is a closed immersion by Stacks 0D5B. -/
@[stacks 0DPZ "closed immersion, given Stacks 0D3Z"]
theorem isClosedImmersion_polarizedCurvesToPolarized
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids) :
    Stack.IsClosedImmersion B integerBase hZ (polarizedCurvesToPolarized B hZ h3Z) :=
  Stack.isClosedImmersion_baseChange.{u, u + 1, u + 1} B integerBase hZ
    (curvesFiberedCategory B hZ) (cartesianProperFlatFiberedCategory B integerBase hZ)
    (polarizedFiberedCategory B hZ h3Z) (curvesToCartesianProperFlatHom B hZ)
    (polarizedToCartesianProperFlatHom B hZ h3Z) (polarizedCurvesSquare B hZ h3Z)
    (isTwoFibreProduct_polarizedCurvesSquare B hZ h3Z)
    (isClosedImmersion_curvesToCartesianProperFlat B hZ)

end AlgebraicGeometry

end
