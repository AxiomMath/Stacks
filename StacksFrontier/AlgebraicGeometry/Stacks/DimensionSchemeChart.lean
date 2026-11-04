module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness

/-!
# The dimension formula of Stacks 0DRJ at a smooth chart by a scheme of the site

**Stacks 0DRJ** computes the dimension of Stacks 0AFN of a locally Noetherian algebraic stack
`𝒳` at a point `x` from any smooth chart through `x`: `dim_x(𝒳) = dim_u(U) - dim_u(U_x)`. The
library proves it for a chart by an *algebraic space*
(`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`, with the relative
dimension produced in
`AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`). This file
reads the same formula off a chart by a *scheme* `U` of the site, where the left-hand side is
indexed by a point of the topological space of `U` itself and the first term of the right-hand
side is the local Krull dimension of that scheme.

## Main results

* `AlgebraicGeometry.Stack.exists_smooth_algebraicSpaceStack_hom_pointsMap_eq`: a smooth chart
  by the algebraic stack of a scheme of the site is a smooth chart by the algebraic space that
  scheme represents, compatibly with the two identifications of the points of either model with
  the points of the scheme. This is the converse direction of
  `AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`.
* `AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth_schemeChart`
  is **Stacks 0DRJ** at a smooth chart by a scheme of the site.

## Implementation notes

A scheme `U` of the site is an algebraic stack in two ways — as the slice
`AlgebraicGeometry.Stack.schemeFibredCategory`, packaged as
`AlgebraicGeometry.Stack.schemeStack`, and as the category of elements
`AlgebraicGeometry.Stack.fibredCategory` of the algebraic space `yoneda.obj U` it represents,
packaged as `AlgebraicGeometry.Stack.algebraicSpaceStack`. Both represent the presheaf
`yoneda.obj U`, so **Stacks 04SW** attaches to the identity of that presheaf a 1-morphism `c`
from the second model to the first, and `c` is smooth by the converse half of **Stacks 06FM**
for representable source and target,
`AlgebraicGeometry.Stack.isSmooth_of_isSmooth_representingMap`. The chart by the algebraic space
is then `c` followed by the given chart, and the comparison on points is the naturality of
**Stacks 04XL** along `c`, whose induced morphism of representing presheaves is the identity.

The relative dimension of Stacks 0DRG is not a hypothesis: it is produced, by
`AlgebraicGeometry.Stack.exists_relativeDimensionAt_eq_natCast`, which is what makes the formula
available at a scheme chart with no input beyond smoothness. The local dimension of the chart
replaces the dimension of Stacks 04N5 of the algebraic space `yoneda.obj U` by
`AlgebraicGeometry.Stack.dimensionAtPoint_yoneda_eq_topologicalKrullDimAt`, and the point of
`|𝒳|` is the image of `u` under
`AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`, the chart map on points read out of the
topological space of the scheme along `AlgebraicGeometry.Stack.pointsHomeomorphScheme`.

## References

* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth chart by the algebraic stack of a scheme of the site is a smooth chart by the
algebraic space that scheme represents**, compatibly with the two identifications of the points
of either model with the points of the scheme.

The 1-morphism `c` between the two models is the one **Stacks 04SW** attaches to the identity of
the presheaf both of them represent; it is smooth because that identity is, by the converse half
of **Stacks 06FM**, and the chart asked for is `c` followed by the given one. Compatibility on
points is the naturality of **Stacks 04XL** along `c`, whose induced morphism of representing
presheaves is the identity by construction.

This is the converse direction of
`AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`. -/
theorem exists_smooth_algebraicSpaceStack_hom_pointsMap_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    ∃ a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳,
      AlgebraicStacks.IsSmooth B S hS a ∧
        ∀ q : Space.points B S hS (yoneda.obj U),
          pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
              (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
              (stackPointOfSpacePoint B S hS (yoneda.obj U) q) =
            pointsMap B S hS (schemeFibredCategory B S hS U).val
              (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
              (representedChartPointMap B S hS U q) := by
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (𝒴 := schemeStack.{u, w} B S hS U)
    (yoneda.obj U) (yoneda.obj U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (representedChart B S hS U)
    (𝟙 (yoneda.obj U))
  have hcsm : AlgebraicStacks.IsSmooth B S hS c := by
    refine isSmooth_of_isSmooth_representingMap B S hS (yoneda.obj U) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (representedChart B S hS U) c ?_
    rw [hc]
    exact Space.isSmooth_id B S hS (isAlgebraicSpace_yoneda B S hS U)
  refine ⟨c ≫ f, AlgebraicStacks.isSmooth_comp B S hS c f hcsm hf, fun q => ?_⟩
  have hnat := spacePointMap_representing_naturality B S hS (yoneda.obj U) (yoneda.obj U)
    (fibredCategory B S hS (yoneda.obj U)) (schemeFibredCategory B S hS U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (representedChart B S hS U) c.hom q
  rw [hc, Space.pointsMap_id, id_eq] at hnat
  exact (pointsMap_comp B S hS (fibredCategory B S hS (yoneda.obj U)).val
    (fibredCategory B S hS (yoneda.obj U)).property
    (schemeFibredCategory B S hS U).property 𝒳.val.property
    c.hom.hom f.hom.hom (stackPointOfSpacePoint B S hS (yoneda.obj U) q)).symm.trans <|
    congrArg (pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom) hnat.symm

/-- **The chart map on points of a scheme chart, read on a point of the representable algebraic
space.** The chart map of `AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap` at the point of
the scheme named by `q` is the image of the corresponding point of the algebraic stack of the
scheme. -/
theorem chartPointMap_pointsToScheme (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (q : Space.points B S hS (yoneda.obj U)) :
    AlgebraicStacks.chartPointMap B S hS U 𝒳 f (Space.pointsToScheme B S hS U q) =
      pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
        (representedChartPointMap B S hS U q) := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  have hpt : (pointsHomeomorphScheme B S hS U).symm
      (Space.pointsToScheme B S hS U q) = representedChartPointMap B S hS U q := by
    rw [← pointsHomeomorphScheme_representedChartPointMap B S hS U q]
    exact (pointsHomeomorphScheme B S hS U).symm_apply_apply _
  exact congrArg (pointsMap B S hS (schemeFibredCategory B S hS U).val
    (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom) hpt

/-- **Stacks 0DRJ at a smooth chart by a scheme of the site.** Let `𝒳` be a locally Noetherian
algebraic stack over `S`, let `f : U ⟶ 𝒳` be a smooth 1-morphism from the algebraic stack of a
scheme `U` of the site, and let `u ∈ U`. Then the relative dimension of Stacks 0DRG at `u` is a
natural number `d` and

`dim_{f(u)}(𝒳) = dim_u(U) - d`,

the first term being the dimension of Stacks 0AFN and the second the local Krull dimension of the
scheme `U` at `u`.

The two models of `U` as an algebraic stack are compared by
`AlgebraicGeometry.Stack.exists_smooth_algebraicSpaceStack_hom_pointsMap_eq`, which turns `f`
into a smooth chart by the algebraic space `yoneda.obj U` through the same point of `|𝒳|`; the
formula is then `AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`
there, with the dimension of Stacks 04N5 of `yoneda.obj U` identified with the local Krull
dimension of `U` by
`AlgebraicGeometry.Stack.dimensionAtPoint_yoneda_eq_topologicalKrullDimAt`. Local finite type of
the chart, which Stacks 0DRG needs to speak of its relative dimension, is a consequence of
smoothness by **Stacks 06MH**. -/
@[stacks 0DRJ "dimension via a smooth scheme chart"]
theorem exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth_schemeChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ d : ℕ,
      dimensionAtPoint B S hS 𝒳 h𝒳 (AlgebraicStacks.chartPointMap B S hS U 𝒳 f u) =
        dimensionSubNat (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u) d := by
  obtain ⟨a, hasm, hapt⟩ :=
    exists_smooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒳 U f hf
  have hqu : Space.pointsToScheme B S hS U ((Space.pointsEquivScheme B S hS U).symm u) = u :=
    (Space.pointsEquivScheme B S hS U).apply_symm_apply u
  obtain ⟨d, -, hd⟩ := exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳
    _ (isAlgebraicSpace_yoneda B S hS U) a hasm
    (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm)
    ((Space.pointsEquivScheme B S hS U).symm u) rfl
  refine ⟨d, ?_⟩
  rw [← hqu, chartPointMap_pointsToScheme B S hS 𝒳 U f, ← hapt, hd,
    dimensionAtPoint_yoneda_eq_topologicalKrullDimAt]

end AlgebraicGeometry.Stack

end
