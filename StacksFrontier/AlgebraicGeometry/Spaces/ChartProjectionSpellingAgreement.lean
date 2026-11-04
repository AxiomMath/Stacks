module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit

/-!
# The two chart projections of a direct image agree

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `V` be an étale scheme chart of `Y`.  The sections of the direct image
`f_*F` of a sheaf of sets over `V` are a limit over the étale scheme charts of `X` above the
algebraic space `X ×_Y V`, the limit cone being
`AlgebraicGeometry.Space.ranChartCone`.  This development projects that limit in **two**
spellings, which were introduced for different purposes and were never compared:

* `AlgebraicGeometry.Space.chartSetProj`, which projects at the *initial* index
  `AlgebraicGeometry.Space.smallBaseChangeIndex` — the base-changed chart `V ×_Y X` itself,
  available when `f` is representable — through
  `AlgebraicGeometry.Space.chartRanApp`;
* `AlgebraicGeometry.Space.moduleChartProjection`, which projects at an *arbitrary* index, and
  whose consumers reach that index from a chart diagram through
  `AlgebraicGeometry.Space.indexOfChartDiagram`.

The two are prefixed by what look like two different comparisons of the direct image with its
right Kan extension form — `AlgebraicGeometry.Space.smallEtaleComparisonRanIso` for the first
and `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` for the second.  They are not
different: `smallEtaleDirectImageRanIso` is `smallEtaleComparisonRanIso` whiskered by the
spaces-étale direct image followed by the comparison restriction of Stacks 03G1, and on
sections over `V` that whiskering is evaluation at the base-changed chart
`AlgebraicGeometry.Space.chartBaseChange`, which is the object the first comparison is already
evaluated at.  So the two projections agree on the nose at the initial index, and at any other
index they differ by the transition map of the limit cone.

## Main results

* `AlgebraicGeometry.Space.chartSetProj_eq_moduleChartProjection`: **the two spellings agree at
  the base-changed chart.**  For a representable `f`, the chart projection of
  `AlgebraicGeometry.Space.chartSetProj` is `AlgebraicGeometry.Space.moduleChartProjection` at
  the index `AlgebraicGeometry.Space.smallBaseChangeIndex`.
* `AlgebraicGeometry.Space.moduleChartProjection_eq_map_chartSetProj`: **the general form.**  At
  an arbitrary index `j`, `moduleChartProjection` is `chartSetProj` followed by restriction
  along the unique morphism of charts from the base-changed chart to `j`, which exists because
  the base-changed chart is an initial index
  (`AlgebraicGeometry.Space.smallBaseChangeIndex_isInitial`).
* `AlgebraicGeometry.Space.moduleChartProjection_indexOfChartDiagram_eq_map_chartSetProj`: the
  same read at the index named by a chart diagram, which is the spelling the consumers of
  `moduleChartProjection` carry.

## Implementation notes

**No declaration here carries a `stacks` attribute.**  Nothing is asserted about a morphism of
algebraic spaces: these are three equations between two spellings of one limit projection.

They were recorded as missing.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonical.lean` list three
steps that the canonical form of **Stacks 073K, part (2)** still needs, and say of the third —
"that those two chart projections — one indexed by the canonical base-change chart through
`AlgebraicGeometry.Space.chartRanApp`, the other by
`AlgebraicGeometry.Space.indexOfChartDiagram` through
`AlgebraicGeometry.Space.moduleChartProjection` — agree at the base-change chart diagram" —
that **no lemma in the tree states that**, and that it is the one of the three that is not a
rewrite with an existing equation.  This file states it.  It does **not** prove either clause of
Stacks 073K: the canonical form of part (2) needs the other two steps and the assembly as well,
and part (1) needs in addition the restriction compatibility of the base change map of
**Stacks 0736**, which this development does not have in any form — see the keyed note on
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/OrdinaryLocality.lean`), which
records that clause (2) of Stacks 0EZR, the same statement for sheaves of sets, has no proof
content anywhere in the repository.

*Why the first equation is one rewrite and a `rfl`.*
`AlgebraicGeometry.Space.moduleChartProjection_app` already expresses the second spelling as the
cone projection after `smallEtaleDirectImageRanIso`, and
`AlgebraicGeometry.Space.chartRanApp` is the cone projection at the initial index by definition,
so after that rewrite both sides are the same cone projection applied to two spellings of the
same section, and the whiskering described above is definitional.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The two chart projections of a direct image agree at the base-changed chart.**  For a
representable `f`, the chart projection `AlgebraicGeometry.Space.chartSetProj` — the projection
of the limit of chart sections to its initial index, the base-changed chart `V ×_Y X` — is
`AlgebraicGeometry.Space.moduleChartProjection` at the index
`AlgebraicGeometry.Space.smallBaseChangeIndex` that names that chart.

Both are the projection of the cone `AlgebraicGeometry.Space.ranChartCone` at that index; the
two comparisons of the direct image with its right Kan extension form that prefix them agree on
sections over `V`, `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` being
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso` whiskered by two functors whose effect on
those sections is evaluation at the base-changed chart. -/
theorem chartSetProj_eq_moduleChartProjection (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (z : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op V)) :
    chartSetProj B S hS f hrep F V z =
      (moduleChartProjection B S hS f V (smallBaseChangeIndex B S hS f hrep V)).app F z := by
  rw [moduleChartProjection_app]
  rfl

/-- **The chart projection at an arbitrary index is the projection at the base-changed chart,
restricted.**  For a representable `f` the base-changed chart is an initial index
(`AlgebraicGeometry.Space.smallBaseChangeIndex_isInitial`), so every étale scheme chart of `X`
above `X ×_Y V` receives a unique morphism from it, and the limit cone's transition along that
morphism carries `AlgebraicGeometry.Space.chartSetProj` to
`AlgebraicGeometry.Space.moduleChartProjection` at that index.

This is the general form of `AlgebraicGeometry.Space.chartSetProj_eq_moduleChartProjection`,
which is the case `j = smallBaseChangeIndex …` with the transition the identity. -/
theorem moduleChartProjection_eq_map_chartSetProj (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (z : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app F z =
      F.obj.map ((smallBaseChangeIndex_isInitial B S hS f hrep V).to j).right
        (chartSetProj B S hS f hrep F V z) := by
  rw [moduleChartProjection_app, ← (ranChartCone B S hS X F.obj
    (chartBaseChange B S hS f V)).w ((smallBaseChangeIndex_isInitial B S hS f hrep V).to j)]
  rfl

/-- **The two chart projections agree at the chart diagram of the base-changed chart.**  The
index that a chart diagram names is `AlgebraicGeometry.Space.indexOfChartDiagram`, and this is
`AlgebraicGeometry.Space.moduleChartProjection_eq_map_chartSetProj` read there: the projection
at the index of a chart diagram over `V` is `AlgebraicGeometry.Space.chartSetProj` followed by
restriction along the unique morphism of charts from the base-changed chart.

This is the spelling in which the consumers of `moduleChartProjection` carry their index —
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection` is stated
through it — so it is the form the comparison is needed in. -/
theorem moduleChartProjection_indexOfChartDiagram_eq_map_chartSetProj (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (z : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op d.V)) :
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app F z =
      F.obj.map ((smallBaseChangeIndex_isInitial B S hS f hrep d.V).to
          (indexOfChartDiagram B S hS f d)).right
        (chartSetProj B S hS f hrep F d.V z) :=
  moduleChartProjection_eq_map_chartSetProj B S hS f hrep F d.V
    (indexOfChartDiagram B S hS f d) z

end AlgebraicGeometry.Space

end
