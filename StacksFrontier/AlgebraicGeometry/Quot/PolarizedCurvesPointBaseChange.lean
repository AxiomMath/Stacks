module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The base change of `PolarizedCurves ⟶ 𝒞urves` along a point is a base change of `𝒫olarized`

*PolarizedCurves* is the 2-fibre product `𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized` of
**Stacks 0DPY** (`AlgebraicGeometry.polarizedCurvesSquare`). So for a point
`g : 𝒰 ⟶ 𝒞urves` of the stack of curves, pasting (**Stacks 003Q**) identifies the base change

  `𝒰 ×_{𝒞urves} PolarizedCurves`

with the base change `𝒰 ×_{𝒮paces'} 𝒫olarized` of the forgetful 1-morphism of **Stacks 0D3Y**
along the composite point `𝒰 ⟶ 𝒞urves ⟶ 𝒮paces'`. The identification is on the nose and not
merely up to equivalence: pasting along the second projection leaves the apex and the second leg
of the inner square unchanged (`CategoryTheory.Bicategory.TwoCommSq.paste_snd`), so the pasted
rectangle *is* the canonical base change of `PolarizedCurves ⟶ 𝒞urves` with its projection to
`𝒰`, read as a square over the outer cospan.

## Implementation notes

`AlgebraicGeometry.polarizedCurvesSquare` lives in the 2-category of categories fibred in
groupoids with morphisms in `Type (u + 1)`, which is where
`AlgebraicGeometry.CurveFamily`, `AlgebraicGeometry.PolarizedFamilyUp` and
`AlgebraicGeometry.CartesianProperFlatSpaces` have their morphisms, so the point `𝒰` here has to
have its morphisms there too. The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` asks for
morphisms in `Type u`, and the 1-morphism
`AlgebraicGeometry.polarizedCurvesToCurvesAlgebraic` is accordingly built between the
hom-shrunk models `AlgebraicGeometry.polarizedCurvesSmall` and
`AlgebraicGeometry.curvesSmall`. The statements below are about the unshrunk square.

## Main definitions

* `AlgebraicGeometry.polarizedCurvesPointSquare`: the canonical base change of
  `PolarizedCurves ⟶ 𝒞urves` along a point of `𝒞urves`.
* `AlgebraicGeometry.polarizedPointSquareOfCurvesPoint`: the same square read over the cospan of
  the forgetful 1-morphism of Stacks 0D3Y and the composite point `𝒰 ⟶ 𝒮paces'`.

## Main results

* `AlgebraicGeometry.isTwoFibreProduct_polarizedCurvesPointSquare`: the first square is a
  2-fibre product, being the canonical one.
* `AlgebraicGeometry.polarizedPointSquareOfCurvesPoint_snd`: the projection to `𝒰` is unchanged
  by the rereading.
* `AlgebraicGeometry.isTwoFibreProduct_polarizedPointSquareOfCurvesPoint`: the rereading is a
  2-fibre product over the outer cospan, so
  `𝒰 ×_{𝒞urves} PolarizedCurves ⟶ 𝒰` is the base change `𝒰 ×_{𝒮paces'} 𝒫olarized ⟶ 𝒰`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0DPY](https://stacks.math.columbia.edu/tag/0DPY)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)
  {𝒰 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ)}

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along a point of `𝒞urves`: the canonical
2-commutative square of Stacks 0040 over the cospan of the point `g` and the projection
`AlgebraicGeometry.polarizedCurvesSquare`.`snd` of Stacks 0DPY. Its first leg is the projection
`𝒰 ×_{𝒞urves} PolarizedCurves ⟶ 𝒰`. -/
def polarizedCurvesPointSquare (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    Bicategory.TwoCommSq g (polarizedCurvesSquare B hZ h3Z).snd :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} g
    (polarizedCurvesSquare B hZ h3Z).snd

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along a point of `𝒞urves` is a 2-fibre
product, being the canonical one (**Stacks 003Q**). -/
def isTwoFibreProduct_polarizedCurvesPointSquare (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    Bicategory.IsTwoFibreProduct (polarizedCurvesPointSquare B hZ h3Z g) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} g
    (polarizedCurvesSquare B hZ h3Z).snd

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along a point of `𝒞urves`, read as a square
over the cospan of the forgetful 1-morphism of Stacks 0D3Y and the composite point
`𝒰 ⟶ 𝒞urves ⟶ 𝒮paces'_{fp, flat, proper}`. It is the rectangle obtained by pasting the
defining square of *PolarizedCurves* (Stacks 0DPY) with that base change; its apex and its
projection to `𝒰` are those of the base change unchanged. -/
def polarizedPointSquareOfCurvesPoint (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    Bicategory.TwoCommSq (polarizedToCartesianProperFlatHom B hZ h3Z)
      (g ≫ curvesToCartesianProperFlatHom B hZ) :=
  (polarizedCurvesSquare B hZ h3Z).paste (polarizedCurvesPointSquare B hZ h3Z g).swap

/-- The apex of the rereading is the apex of the base change. -/
theorem polarizedPointSquareOfCurvesPoint_pt (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    (polarizedPointSquareOfCurvesPoint B hZ h3Z g).pt =
      (polarizedCurvesPointSquare B hZ h3Z g).pt :=
  rfl

/-- The second leg of the pasted rectangle is the
first leg of the base change of `PolarizedCurves ⟶ 𝒞urves`, that is, the projection
`𝒰 ×_{𝒞urves} PolarizedCurves ⟶ 𝒰`. -/
theorem polarizedPointSquareOfCurvesPoint_snd (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    (polarizedPointSquareOfCurvesPoint B hZ h3Z g).snd =
      (polarizedCurvesPointSquare B hZ h3Z g).fst :=
  rfl

/-- The base change of `PolarizedCurves ⟶ 𝒞urves` along a point `g` of `𝒞urves`, reread over the
cospan of the forgetful 1-morphism of Stacks 0D3Y and the composite point
`g ≫ (𝒞urves ⟶ 𝒮paces'_{fp, flat, proper})`, is a 2-fibre product of that cospan. So
`𝒰 ×_{𝒞urves} PolarizedCurves ⟶ 𝒰` is the base change of `𝒫olarized ⟶ 𝒮paces'` along
`𝒰 ⟶ 𝒮paces'`. -/
def isTwoFibreProduct_polarizedPointSquareOfCurvesPoint
    (g : 𝒰 ⟶ curvesFiberedCategory B hZ) :
    Bicategory.IsTwoFibreProduct (polarizedPointSquareOfCurvesPoint B hZ h3Z g) :=
  Bicategory.isTwoFibreProduct_paste (isTwoFibreProduct_polarizedCurvesSquare B hZ h3Z)
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_polarizedCurvesPointSquare B hZ h3Z g))

end AlgebraicGeometry

end
