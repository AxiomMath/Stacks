module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Flatness over the target at a point may be read on any chart diagram

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be a quasi-coherent `𝒪_X`-module. `AlgebraicGeometry.Space.IsFlatOverAtPoint`, flatness of
`F` over `Y` at a point, is stated by existentially quantifying over commuting squares of étale
scheme charts. The condition does not depend on the square: at the point cut out by a point `u`
of the source chart of one square it holds exactly when the restriction of `F` to that square's
source chart is flat over its target chart at `u`.

For a morphism `α : W ⟶ V` of the big fppf site, the condition at a point of the algebraic space
`h_W` is flatness, in the ringed-space sense, of the comparison
`AlgebraicGeometry.Space.representedZariskiRestriction` of the module over the morphism of
representing schemes at the corresponding point of the scheme `W`.

## Main definitions

* `AlgebraicGeometry.Space.selfChartDiagram`: a morphism of the big fppf site, read as a
  commuting square of étale scheme charts of the induced morphism of represented algebraic
  spaces — the identity chart on each side.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram`: the condition at a
  point of the source chart of an arbitrary chart diagram.
* `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction`: the
  represented case, against `AlgebraicGeometry.IsFlatOverAt` on the representing morphism of
  schemes.
* `AlgebraicGeometry.Space.pointOfEtaleChart_selfChart`: the point of a represented algebraic
  space cut out through the identity chart is its image under the comparison bijection
  `AlgebraicGeometry.Space.pointsEquivScheme`.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading the condition on one chart diagram -/

/-- For a quasi-coherent `𝒪_X`-module `F`, a commuting square `d` of étale scheme charts of `f`
and a point `u` of its source chart, the module is flat over `Y` at the point of `|X|` cut out by
`u` exactly when the restriction of `F` to the source chart is flat over the target chart at
`u`. -/
theorem isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (u : etaleChartScheme B S hS d.U) :
    IsFlatOverAtPoint B S hS X.2 f.hom F (pointOfEtaleChart B S hS d.U u) ↔
      IsFlatOverAtOnChartDiagram B S hS X.2 F d u :=
  have := hF
  (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).symm

/-! ### The identity chart diagram of a morphism of represented algebraic spaces -/

/-- A morphism `α : W ⟶ V` of the big fppf site, read as a commuting square of étale scheme
charts of the induced morphism `h_α` of represented algebraic spaces: the identity chart on
each side, joined by `α` itself. -/
def selfChartDiagram {W V : BigFppfOver B S hS} (α : W ⟶ V) :
    ChartDiagram B S hS (yoneda.obj W) (yoneda.obj V) (yoneda.map α) where
  U := selfChart B S hS W
  V := selfChart B S hS V
  g := α
  comm := (Category.id_comp (yoneda.map α)).trans (Category.comp_id (yoneda.map α)).symm

/-- The point of a represented algebraic space cut out by a point of the representing scheme,
read through the identity chart, is its image under the comparison bijection
`AlgebraicGeometry.Space.pointsEquivScheme`. -/
theorem pointOfEtaleChart_selfChart (W : BigFppfOver B S hS)
    (u : (BigFppfOver.toScheme B S hS).obj W) :
    pointOfEtaleChart B S hS (selfChart B S hS W) u = (pointsEquivScheme B S hS W).symm u :=
  pointsMap_id_apply B S hS ((pointsEquivScheme B S hS W).symm u)

/-- For a morphism `α : W ⟶ V` of the big fppf site and a quasi-coherent `𝒪`-module `G` on the
small étale site of `h_W`, the module is flat over `h_V` at the point of `|h_W|` cut out, through
the identity chart, by a point `u` of the scheme `W` exactly when
`AlgebraicGeometry.Space.representedZariskiRestriction` of `G` is flat, in the ringed-space
sense, over the morphism of representing schemes at `u`. -/
theorem isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction
    {W V : BigFppfOver B S hS} (α : W ⟶ V)
    (G : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) (u : (BigFppfOver.toScheme B S hS).obj W) :
    IsFlatOverAtPoint B S hS (isAlgebraicSpace_yoneda B S hS W) (yoneda.map α) G
        (pointOfEtaleChart B S hS (selfChart B S hS W) u) ↔
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
        (representedZariskiRestriction B S hS W (isAlgebraicSpace_yoneda B S hS W) G) u :=
  isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS
    (X := schemeSpace W) (Y := schemeSpace V) (schemeSpaceMap α) G hG
    (selfChartDiagram B S hS α) u

end AlgebraicGeometry.Space

end
