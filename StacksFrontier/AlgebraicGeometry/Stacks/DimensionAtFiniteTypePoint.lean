module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancyStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.Exercises.NonExercises.DimensionFiniteTypePoint

/-!
# The dimension of an algebraic stack is attained at a finite type point

Let `𝒳` be a locally Noetherian algebraic stack over `S` and let `x ∈ |𝒳|`. **Stacks 0DS1**
says that every open substack `𝒱 ⊆ 𝒳` containing `x` already contains a finite type point `x₀`
with `dim_{x₀}(𝒳) = dim_x(𝒱)`.

The source proves it by passing to a smooth chart of `𝒱`. A smooth surjective 1-morphism from a
scheme is open and surjective on points and carries finite type points to finite type points, so
it suffices to find, inside a neighbourhood of a chart point `u` above `x`, a point `u₀` which is
a finite type point of the chart and at which the dimension formula gives the same value. Two
shrinkings make that possible: the relative dimension of the chart is constant near `u`
(Stacks 0DRQ (2)), and the local dimension of the chart at `u` is attained at a locally closed
point of any neighbourhood of `u`.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_yoneda_eq_topologicalKrullDimAt`: the dimension of
  Stacks 04N5 of the algebraic space a scheme of the site represents is the Krull dimension of
  that scheme at the corresponding point.
* `AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`: a smooth chart by the
  algebraic space a scheme of the site represents is a smooth chart by the algebraic stack of
  that scheme, compatibly on points.
* `AlgebraicGeometry.Stack.exists_isSmooth_algebraicSpaceStack_hom_chartPointMap_eq`: the mirror of
  the previous result — a smooth chart by the algebraic stack of a scheme of the site is a smooth
  chart by the algebraic space that scheme represents, compatibly on points.
* `AlgebraicGeometry.Stack.isFiniteTypePoint_pointsMap_of_space_isFiniteTypePoint`: a finite type
  point of a smooth scheme chart has a finite type point of the stack as its image.
* `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_dimensionAtPoint_eq`: the dimension of a
  locally Noetherian algebraic stack at a point is its dimension at some finite type point —
  Stacks 0DS1 with the open substack taken to be the whole stack.
* `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_mem_pointSet_dimensionAtPoint_eq` is
  **Stacks 0DS1**.

## Implementation notes

**The two shrinkings.** The source shrinks the chart twice, and both shrinkings are performed here
on the point rather than on the chart, so that no chart has to be restricted to an open
subscheme. Constancy of the relative dimension is **Stacks 0DRQ (2)** for a 1-morphism from an
algebraic space to an algebraic *stack*,
`AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack`: it
produces an open set `O` of chart points on which the relative dimension equals its value at `u`.
The second shrinking is `AlgebraicGeometry.exists_isLocallyClosed_topologicalKrullDimAt_eq`, which
produces inside `O` a point `u₀` whose singleton is locally closed in the chart and at which the
chart has the local dimension it has at `u`; the source reaches the same point by shrinking until
`dim_u(U) = dim(U)` and applying **Stacks 0DRR**, which is what that lemma does when the local
dimension is finite. With both in hand the dimension formula of **Stacks 0DRJ** reads the
dimension of the stack at the images of `u₀` and of `u` with the same minuend and the same
subtrahend.

**The finite type point.** A point whose singleton is locally closed in the chart is a finite type
point of the algebraic space the chart scheme represents, by **Stacks 06EK** applied to that
singleton; `AlgebraicGeometry.Stack.isFiniteTypePoint_pointsMap_of_space_isFiniteTypePoint` then
makes its image a finite type point of the stack. That step goes through **Stacks 06EF**, which
exhibits the point as the image of a closed point of a scheme étale over the chart, and
**Stacks 06FX**, which asks for the chart in the `AlgebraicGeometry.Stack.schemeStack` model — the
slice of the site over the scheme — whereas the dimension formula of Stacks 0DRJ asks for it in
the `AlgebraicGeometry.Stack.algebraicSpaceStack` model of the presheaf the scheme represents.
`AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq` bridges the two models: they
represent the same presheaf, so Stacks 04SW attaches to its identity a 1-morphism between them,
smooth by the converse half of Stacks 06FM, and the naturality of Stacks 04XL identifies the two
maps on points.

**From the chart to the open substack.** The reduction to a chart is applied to `𝒱` itself, whose
local Noetherianity is **Stacks 0CPM**; the chart is the locally Noetherian smooth surjective
scheme atlas of **Stacks 04YG** that local Noetherianity provides. Passing back to `𝒳` uses two
properties of the inclusion of an open substack: it is locally of finite type, so it carries
finite type points to finite type points (**Stacks 06G0**), and it leaves the dimension of
Stacks 0AFN unchanged, which is
`AlgebraicGeometry.Stack.dimensionAtPoint_pointsMap_eq_of_isOpenImmersion`.

**The chart-level form.**
`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_dimensionAtPoint_eq_of_relativeDimension_const`
is the reduced goal the source's own proof reaches, on a chart already in the position its two
shrinkings produce: there the relative dimension is constant on the whole chart and the chart is
finite dimensional with its dimension attained at the given point, and the point produced is
closed in the chart. It is a statement about a chart and not about an open substack, and
Stacks 0DS1 above does not go through it — the shrinkings are performed at the point instead,
which is what lets a chart of infinite dimension be handled at all.

The universe `u` is that of the base scheme and of its relative big fppf site, while `w` is the
descent universe at which algebraicity of `𝒳` is tested; the two are independent.

## References

* [Stacks Project, Tag 02J1](https://stacks.math.columbia.edu/tag/02J1)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRR](https://stacks.math.columbia.edu/tag/0DRR)
* [Stacks Project, Tag 0DS1](https://stacks.math.columbia.edu/tag/0DS1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The dimension of **Stacks 04N5** of the algebraic space represented by a scheme `U` of the
site, at a point, is the Krull dimension of `U` at the corresponding point: the identity is an
étale chart of the represented presheaf. -/
theorem dimensionAtPoint_yoneda_eq_topologicalKrullDimAt (U : BigFppfOver B S hS)
    (q : Space.points B S hS (yoneda.obj U)) :
    Space.dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) q =
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
        (Space.pointsToScheme B S hS U q) := by
  have hid : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (𝟙 (yoneda.obj U)) :=
    Space.presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj U))
  revert q
  refine Quot.ind fun p => ?_
  exact Space.dimensionAtPoint_eq_of_etale_chart B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) _ U (𝟙 _) hid p
    (by rw [Space.pointsMap_id]; rfl)

/-- Precomposing a smooth 1-morphism with the 1-morphism that **Stacks 04SW** attaches to the
identity of `yoneda.obj U` between two models of it gives a smooth 1-morphism, compatibly with the
maps on points of **Stacks 04XL**. -/
private theorem exists_isSmooth_hom_pointsMap_eq_of_equivalenceOver
    (𝒜 𝒞 𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (eA : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver 𝒞.val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (f : 𝒞 ⟶ 𝒳) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    ∃ g : 𝒜 ⟶ 𝒳, AlgebraicStacks.IsSmooth B S hS g ∧
      ∀ q : Space.points B S hS (yoneda.obj U),
        pointsMap B S hS 𝒜.val.val 𝒜.val.property 𝒳.val.property g.hom.hom
            (spacePointMap B S hS (yoneda.obj U) 𝒜.val
              (representingEquivalence B S hS (yoneda.obj U) 𝒜.val eA).functor q) =
          pointsMap B S hS 𝒞.val.val 𝒞.val.property 𝒳.val.property f.hom.hom
            (spacePointMap B S hS (yoneda.obj U) 𝒞.val
              (representingEquivalence B S hS (yoneda.obj U) 𝒞.val eC).functor q) := by
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS (𝒳 := 𝒜) (𝒴 := 𝒞)
    (yoneda.obj U) (yoneda.obj U) eA eC (𝟙 (yoneda.obj U))
  have hcsm : AlgebraicStacks.IsSmooth B S hS c := by
    refine isSmooth_of_isSmooth_representingMap B S hS (yoneda.obj U) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS U) eA eC c ?_
    rw [hc]
    exact Space.isSmooth_id B S hS (isAlgebraicSpace_yoneda B S hS U)
  refine ⟨c ≫ f, AlgebraicStacks.isSmooth_comp B S hS c f hcsm hf, fun q => ?_⟩
  have hnat := spacePointMap_representing_naturality B S hS (yoneda.obj U) (yoneda.obj U)
    𝒜.val 𝒞.val eA eC c.hom q
  rw [hc, Space.pointsMap_id, id_eq] at hnat
  exact (pointsMap_comp B S hS 𝒜.val.val 𝒜.val.property 𝒞.val.property 𝒳.val.property
    c.hom.hom f.hom.hom _).symm.trans (congrArg (pointsMap B S hS 𝒞.val.val 𝒞.val.property
      𝒳.val.property f.hom.hom) hnat).symm

/-- **A smooth chart by the algebraic space a scheme of the site represents is a smooth chart
by the algebraic stack of that scheme**, compatibly with the two identifications of the points
of either model with the points of the scheme.

The 1-morphism `c` between the two models is the one **Stacks 04SW** attaches to the identity of
the presheaf both of them represent; it is smooth because that identity is, by the converse half
of **Stacks 06FM**, and the chart asked for is `c` followed by the given one. Compatibility on
points is the naturality of **Stacks 04XL** along `c`, whose induced morphism of representing
presheaves is the identity by construction. -/
theorem exists_smooth_schemeStack_hom_pointsMap_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) :
    ∃ φ : schemeStack.{u, w} B S hS U ⟶ 𝒳,
      AlgebraicStacks.IsSmooth B S hS φ ∧
        ∀ q : Space.points B S hS (yoneda.obj U),
          pointsMap B S hS (schemeFibredCategory B S hS U).val
              (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom
              (representedChartPointMap B S hS U q) =
            pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
              (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
              (stackPointOfSpacePoint B S hS (yoneda.obj U) q) := by
  exact exists_isSmooth_hom_pointsMap_eq_of_equivalenceOver.{u, w} B S hS
    (schemeStack.{u, w} B S hS U) (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) 𝒳 U (representedChart B S hS U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) a hasm

/-- **A smooth chart by the algebraic stack of a scheme of the site is a smooth chart by the
algebraic space that scheme represents**, compatibly with the two identifications of the points
of either model with the points of the scheme.

This is the mirror of `AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`, read
in the other direction. The 1-morphism `e` out of the algebraic-space model is again the one
**Stacks 04SW** attaches to the identity of the presheaf both models represent; it is smooth
because that identity is, by the converse half of **Stacks 06FM**, and the chart asked for is `e`
followed by the given one. Compatibility on points is the naturality of **Stacks 04XL** along
`e`, whose induced morphism of representing presheaves is the identity by construction. -/
theorem exists_isSmooth_algebraicSpaceStack_hom_chartPointMap_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    ∃ g : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳,
      AlgebraicStacks.IsSmooth B S hS g ∧
        ∀ q : Space.points B S hS (yoneda.obj U),
          pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
              (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property g.hom.hom
              (stackPointOfSpacePoint B S hS (yoneda.obj U) q) =
            pointsMap B S hS (schemeFibredCategory B S hS U).val
              (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
              (representedChartPointMap B S hS U q) := by
  exact exists_isSmooth_hom_pointsMap_eq_of_equivalenceOver.{u, w} B S hS
    (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (schemeStack.{u, w} B S hS U) 𝒳 U (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representedChart B S hS U) f hf

/-- **A finite type point of a smooth scheme chart has a finite type point of the stack as its
image.** This is condition (2) of **Stacks 06FX** reached from a finite type point of the chart
rather than from a closed one: by **Stacks 06EF** the finite type point is the image of a closed
point of a scheme `V` étale over the chart, and `V ⟶ U ⟶ 𝒳` is then a smooth chart of `𝒳`
carrying that closed point to the same point of `|𝒳|`.

The chart is turned into one in the `AlgebraicGeometry.Stack.schemeStack` model, which is what
Stacks 06FX asks for, by
`AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`. -/
theorem isFiniteTypePoint_pointsMap_of_space_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (y : Space.points B S hS (yoneda.obj U))
    (hy : Space.IsFiniteTypePoint B S hS (yoneda.obj U) y) :
    IsFiniteTypePoint.{u, w} B S hS 𝒳
      (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
        (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
        (stackPointOfSpacePoint B S hS (yoneda.obj U) y)) := by
  obtain ⟨φ, hφsm, hφpt⟩ := exists_smooth_schemeStack_hom_pointsMap_eq.{u, w} B S hS 𝒳 U a hasm
  obtain ⟨V, ψ, t, hψ, hclosed, hψy⟩ :=
    (Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) y).1 hy
  have hgψ : yoneda.map (yoneda.preimage ψ) = ψ := yoneda.map_preimage ψ
  have hψ' : Space.IsEtale B S hS (yoneda.map (yoneda.preimage ψ)) := by rw [hgψ]; exact hψ
  have hψy' : Space.pointsMap B S hS (yoneda.obj V) (yoneda.map (yoneda.preimage ψ))
      (t.class B S hS (yoneda.obj V)) = y := by rw [hgψ]; exact hψy
  have hgetale : Etale ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ψ)) :=
    (Space.presheaf_yoneda_map_etale_iff B S hS (yoneda.preimage ψ)).1
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (yoneda.preimage ψ))).1 hψ')
  refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
    ⟨V, schemeStackMap.{u, w} B S hS (yoneda.preimage ψ) ≫ φ,
      representedChartPointMap B S hS V (t.class B S hS (yoneda.obj V)),
      AlgebraicStacks.isSmooth_comp B S hS _ _
        (isSmooth_schemeStackMap.{u, w} B S hS (yoneda.preimage ψ) inferInstance) hφsm, ?_, ?_⟩
  · rw [pointsHomeomorphScheme_representedChartPointMap]
    exact hclosed
  · refine Eq.trans (Stack.pointsMap_comp B S hS (schemeFibredCategory B S hS V).val
      (schemeFibredCategory B S hS V).property
      (schemeFibredCategory B S hS U).property 𝒳.val.property
      (schemeFibredCategoryMap B S hS (yoneda.preimage ψ)).hom φ.hom.hom _).symm ?_
    refine Eq.trans (congrArg _ ((representedChartPointMap_naturality B S hS
      (yoneda.preimage ψ) (t.class B S hS (yoneda.obj V))).trans
      (congrArg (representedChartPointMap B S hS U) hψy'))) ?_
    exact hφpt y

/-- **Stacks 0DS1, on a smooth scheme chart already shrunk as the source's proof shrinks it.**
Let `𝒳` be a locally Noetherian algebraic stack over `S` and let `a : U ⟶ 𝒳` be a smooth,
locally-of-finite-type 1-morphism from the algebraic space a scheme `U` of the site represents.
Assume the relative dimension of `a` is the constant natural number `m`, that `U` has finite
dimension, and that `U` has at `u` the dimension it has globally. Then `U` has a closed — hence
finite type — point `u₀` whose image in `|𝒳|` is a finite type point at which `𝒳` has the
dimension it has at the image of `u`.

The point is **Stacks 0DRR** applied to `U`; its image is a finite type point of `|𝒳|` by
**Stacks 06FX**, through
`AlgebraicGeometry.Stack.exists_smooth_schemeStack_hom_pointsMap_eq`; and the two dimensions of
`𝒳` are read off `a` at `u₀` and at `u` by the dimension formula of **Stacks 0DRJ**. The two
values agree because the local dimensions of `U` at `u₀` and at `u` are both `dim(U)` and the
relative dimension is the same `m` at both points.

The hypotheses `hm` and `hu` put the chart in the position the source's two shrinkings produce,
and the conclusion is stated at the chart rather than at an open substack of `𝒳`;
`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_mem_pointSet_dimensionAtPoint_eq` below is
Stacks 0DS1 itself, and reaches that position with no hypothesis beyond the source's. -/
theorem exists_isFiniteTypePoint_dimensionAtPoint_eq_of_relativeDimension_const
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (m : ℕ)
    (hm : ∀ q : Space.points B S hS (yoneda.obj U),
      relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha q = (m : WithBot ℕ∞))
    (d : ℕ)
    (hUdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) = d)
    (u : Space.points B S hS (yoneda.obj U))
    (hu : topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
        (Space.pointsToScheme B S hS U u) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ u₀ : Space.points B S hS (yoneda.obj U),
      IsClosed ({Space.pointsToScheme B S hS U u₀} :
          Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        _root_.AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS U u₀) ∧
          IsFiniteTypePoint.{u, w} B S hS 𝒳
              (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
                (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
                (stackPointOfSpacePoint B S hS (yoneda.obj U) u₀)) ∧
            dimensionAtPoint B S hS 𝒳 h𝒳
                (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
                  (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
                  (stackPointOfSpacePoint B S hS (yoneda.obj U) u₀)) =
              dimensionAtPoint B S hS 𝒳 h𝒳
                (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
                  (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
                  (stackPointOfSpacePoint B S hS (yoneda.obj U) u)) := by
  obtain ⟨x₀, hx₀closed, hx₀ft, hx₀dim⟩ :=
    exists_isClosed_isFiniteTypePoint_dim_eq ((BigFppfOver.toScheme B S hS).obj U) d hUdim
  obtain ⟨φ, hφsm, hφpt⟩ :=
    exists_smooth_schemeStack_hom_pointsMap_eq.{u, w} B S hS 𝒳 U a hasm
  have hxeq : Space.pointsToScheme B S hS U
      ((Space.pointsEquivScheme B S hS U).symm x₀) = x₀ :=
    (Space.pointsEquivScheme B S hS U).apply_symm_apply x₀
  refine ⟨(Space.pointsEquivScheme B S hS U).symm x₀, ?_, ?_, ?_, ?_⟩
  · rw [hxeq]; exact hx₀closed
  · rw [hxeq]; exact hx₀ft
  · refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
      ⟨U, φ, representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm x₀),
        hφsm, ?_, hφpt _⟩
    rw [pointsHomeomorphScheme_representedChartPointMap,
      hxeq]
    exact hx₀closed
  · have hdim : Space.dimensionAtPoint B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) ((Space.pointsEquivScheme B S hS U).symm x₀) =
        Space.dimensionAtPoint B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U) u := by
      rw [dimensionAtPoint_yoneda_eq_topologicalKrullDimAt,
        dimensionAtPoint_yoneda_eq_topologicalKrullDimAt, hxeq, hx₀dim, hu]
    rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _
        (isAlgebraicSpace_yoneda B S hS U) a hasm ha
        ((Space.pointsEquivScheme B S hS U).symm x₀) rfl m
        (hm ((Space.pointsEquivScheme B S hS U).symm x₀)),
      dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _
        (isAlgebraicSpace_yoneda B S hS U) a hasm ha u rfl m (hm u),
      hdim]

/-! ### Stacks 0DS1 -/

section ZeroDS1

attribute [local instance] Space.pointTopology

/-- **Stacks 0DS1 with the open substack taken to be the whole stack.** The dimension of a
locally Noetherian algebraic stack `𝒲` at a point is the dimension of `𝒲` at some finite type
point.

The chart is the locally Noetherian smooth surjective scheme atlas that local Noetherianity of
`𝒲` provides (**Stacks 04YG**), read through the algebraic space the chart scheme represents.
Its relative dimension is constant on an open neighbourhood `O` of a chart point `u` above the
given point, by **Stacks 0DRQ (2)** in the form
`AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack` — this
is
the first of the two shrinkings the source's proof performs. The second is
`AlgebraicGeometry.exists_isLocallyClosed_topologicalKrullDimAt_eq`, which produces inside `O` a
point `u₀` whose singleton is locally closed and at which the chart has the local dimension it
has at `u`; that point is a finite type point of the chart by **Stacks 06EK**, and so its image
is a finite type point of `|𝒲|`. The dimension formula of **Stacks 0DRJ** at `u₀` and at `u`
then has the same subtrahend and the same minuend. -/
theorem exists_isFiniteTypePoint_dimensionAtPoint_eq
    (𝒲 : AlgebraicStacks.{u, w} B S hS)
    (h𝒲 : IsLocallyNoetherianStack.{u, w} B S hS 𝒲)
    (x : points B S hS 𝒲.val.val 𝒲.val.property) :
    ∃ x₀ : points B S hS 𝒲.val.val 𝒲.val.property,
      IsFiniteTypePoint.{u, w} B S hS 𝒲 x₀ ∧
        dimensionAtPoint B S hS 𝒲 h𝒲 x₀ = dimensionAtPoint B S hS 𝒲 h𝒲 x := by
  classical
  obtain ⟨U, g, hgsurj, hgsm, hUN⟩ := id h𝒲
  have := hUN
  obtain ⟨e, hesm, hesurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom B S hS U
  have hasm := AlgebraicStacks.isSmooth_comp B S hS e g hesm hgsm
  have ha := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS (e ≫ g) hasm
  obtain ⟨z, hz⟩ := isSurjective_comp B S hS e g hesurj hgsurj x
  obtain ⟨u, hu0⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U)).surjective z
  have hu : pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property 𝒲.val.property (e ≫ g).hom.hom
      (stackPointOfSpacePoint B S hS (yoneda.obj U) u) = x := by rw [← hz, ← hu0]
  -- the first shrinking: the relative dimension of the chart is constant near `u`
  obtain ⟨O, hOopen, huO, hOconst⟩ :=
    (IsLocallyConstant.iff_exists_open _).1
      (isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack.{u, w} B S hS
        (isAlgebraicSpace_yoneda B S hS U) 𝒲 (e ≫ g) hasm ha) u
  -- the second shrinking: a locally closed point of the chart with the same local dimension
  obtain ⟨x₀s, hx₀mem, hx₀lc, hx₀dim⟩ :=
    exists_isLocallyClosed_topologicalKrullDimAt_eq ((BigFppfOver.toScheme B S hS).obj U)
      (Space.pointsToScheme B S hS U u)
      ((Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U O).1 hOopen)
      ⟨u, huO, rfl⟩
  obtain ⟨y₀, hy₀O, hy₀⟩ := hx₀mem
  -- it is a finite type point of the chart, by Stacks 06EK at the singleton
  have hy₀lc : IsLocallyClosed ({y₀} : Set (Space.points B S hS (yoneda.obj U))) := by
    have hpre : Space.pointsToScheme B S hS U ⁻¹' {x₀s} = {y₀} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Space.injective_pointsToScheme B S hS U (h.trans hy₀.symm),
        fun h => by rw [h, hy₀]⟩
    rw [← hpre]
    exact hx₀lc.preimage (Space.schemePointsHomeomorph B S hS U).continuous
  have hy₀ft : Space.IsFiniteTypePoint B S hS (yoneda.obj U) y₀ := by
    obtain ⟨y, hy, hyft⟩ := Space.inter_finiteTypePoints_nonempty B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) hy₀lc (Set.singleton_nonempty y₀)
    rwa [Set.mem_singleton_iff.1 hy] at hyft
  refine ⟨pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property 𝒲.val.property (e ≫ g).hom.hom
      (stackPointOfSpacePoint B S hS (yoneda.obj U) y₀),
    isFiniteTypePoint_pointsMap_of_space_isFiniteTypePoint.{u, w} B S hS 𝒲 U (e ≫ g) hasm y₀
      hy₀ft, ?_⟩
  obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) 𝒲 (e ≫ g) ha u
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒲 h𝒲 _
      (isAlgebraicSpace_yoneda B S hS U) (e ≫ g) hasm ha y₀ rfl m
      ((hOconst y₀ hy₀O).trans hm),
    dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒲 h𝒲 x
      (isAlgebraicSpace_yoneda B S hS U) (e ≫ g) hasm ha u hu m hm,
    dimensionAtPoint_yoneda_eq_topologicalKrullDimAt,
    dimensionAtPoint_yoneda_eq_topologicalKrullDimAt, hy₀, hx₀dim]

/-- **Stacks 0DS1.** Let `𝒳` be a locally Noetherian algebraic stack over `S`, let `𝒱` be an open
substack of `𝒳` and let `x ∈ |𝒱|`. Then there is a finite type point `x₀ ∈ |𝒱|` — a finite type
point both of `𝒱` and of `𝒳` — with `dim_{x₀}(𝒳) = dim_x(𝒱)`.

The point `x` of `|𝒳|` lying in `|𝒱|` is given as a point of `|𝒱|`, which is what membership in
`AlgebraicGeometry.Stack.OpenSubstack.pointSet` says, and `dim_x(𝒱)` is the dimension of
Stacks 0AFN of the open substack read as an algebraic stack; that it is locally Noetherian is
**Stacks 0CPM**, `AlgebraicGeometry.Stack.isLocallyNoetherianStack_toAlgebraicStack`.

The source reduces to a smooth chart of `𝒱` and performs two shrinkings there, which is
`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_dimensionAtPoint_eq` applied to `𝒱`. What
remains is to pass from `𝒱` back to `𝒳`: the inclusion of an open substack is locally of finite
type, so it carries finite type points to finite type points (**Stacks 06G0**), and it leaves the
dimension of Stacks 0AFN unchanged, which is
`AlgebraicGeometry.Stack.dimensionAtPoint_pointsMap_eq_of_isOpenImmersion`. -/
@[stacks 0DS1]
theorem exists_isFiniteTypePoint_mem_pointSet_dimensionAtPoint_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (𝒱 : OpenSubstack 𝒳)
    (x : points B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic).val.val
      (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic).val.property) :
    ∃ x₀ : points B S hS
        (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic).val.val
        (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic).val.property,
      IsFiniteTypePoint.{u, w} B S hS
          (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic) x₀ ∧
        IsFiniteTypePoint.{u, w} B S hS 𝒳
            (AlgebraicStacks.pointsMap B S hS 𝒱.inclusion x₀) ∧
          AlgebraicStacks.pointsMap B S hS 𝒱.inclusion x₀ ∈ 𝒱.pointSet B S hS ∧
            dimensionAtPoint B S hS 𝒳 h𝒳
                (AlgebraicStacks.pointsMap B S hS 𝒱.inclusion x₀) =
              dimensionAtPoint B S hS
                (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic)
                (isLocallyNoetherianStack_toAlgebraicStack B S hS 𝒱 h𝒳) x := by
  obtain ⟨x₀, hx₀ft, hx₀dim⟩ := exists_isFiniteTypePoint_dimensionAtPoint_eq.{u, w} B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒱.property 𝒱.isAlgebraic)
    (isLocallyNoetherianStack_toAlgebraicStack B S hS 𝒱 h𝒳) x
  refine ⟨x₀, hx₀ft, ?_, ⟨x₀, rfl⟩, ?_⟩
  · exact mapsTo_finiteTypePoints B S hS 𝒱.inclusion
      (AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion B S hS 𝒱.inclusion
        𝒱.isOpenImmersion) hx₀ft
  · exact (dimensionAtPoint_pointsMap_eq_of_isOpenImmersion B S hS 𝒱.inclusion 𝒱.isOpenImmersion
      (isLocallyNoetherianStack_toAlgebraicStack B S hS 𝒱 h𝒳) h𝒳 x₀).trans hx₀dim

end ZeroDS1

end AlgebraicGeometry.Stack

end
