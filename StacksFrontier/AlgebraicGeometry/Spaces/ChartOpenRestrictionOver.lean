module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank

/-!
# The chart restriction on a Zariski open of the chart, read on the open itself

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `F` be a quasi-coherent
`𝒪_X`-module, let `A` be an étale scheme chart of `X` and let `W` be a Zariski open of
`chartScheme A`. The restriction of the chart restriction `restrictToChart F A` to `W` is
isomorphic to the chart restriction of `F` at the étale chart `(chartOpens B S hS A).obj W` that
`W` cuts out. This holds for the restriction written as the inverse image along `W.ι`, as the
restriction to the slice of the Zariski site at `W`, and as the restriction to the open subspace.

## Main results

* `AlgebraicGeometry.Space.chartSchemeMap_chartOpensHom`: the morphism of chart schemes
  underlying `AlgebraicGeometry.Space.chartOpensHom` is the inclusion of the open.
* `AlgebraicGeometry.Space.nonempty_pullback_opens_restrictToChart`: the inverse image of the
  chart restriction along `W.ι` is the chart restriction at the chart `W` cuts out.
* `AlgebraicGeometry.Space.nonempty_over_restrictToChart_chartOpens`: the restriction of the
  chart restriction to the slice at `W`, carried to the open subscheme by
  `AlgebraicGeometry.Scheme.Modules.overEquiv`, is that chart restriction.
* `AlgebraicGeometry.Space.nonempty_restrictMod_restrictToChart_chartOpens`: the same for the
  restriction to the open subspace of `LocallyFreeRank.restrictMod`.
* `AlgebraicGeometry.Space.nonempty_over_restrictToChart_chartOpenNeighborhood`: the same at a
  Zariski open of the chart of a small étale neighbourhood, with the chart of
  `AlgebraicGeometry.Space.chartOpenNeighborhood`.

## Implementation notes

The identification is not definitional: the Zariski sheafification defining
`AlgebraicGeometry.Space.restrictToChart` does not commute with the restriction on the nose. The
equalities `chartScheme ((chartOpens B S hS A).obj W) = W.toScheme` and the identification of the
restricted structure sheaf `LocallyFreeRank.restrictRing` with the structure sheaf of that chart
scheme are `rfl`, which is what puts the two modules over one sheaf of rings.

The passage between `AlgebraicGeometry.Space.restrictToChart` and
`AlgebraicGeometry.Space.restrictToChartScheme` uses `CategoryTheory.eqToIso` of a `congrArg`
rather than `rw`: `AlgebraicGeometry.Scheme.Modules` is a `def`, so a rewrite motive mixing it with
`SheafOfModules _` is not type-correct at the transparency `rw` checks it at.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- The morphism of chart schemes underlying `AlgebraicGeometry.Space.chartOpensHom` is the
inclusion of the open. -/
theorem chartSchemeMap_chartOpensHom (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    chartSchemeMap (chartOpensHom B S hS X A V) = V.ι :=
  rfl

/-- The inverse image of the chart restriction along a Zariski open of the chart is the chart
restriction at the étale chart that open cuts out. -/
theorem nonempty_pullback_opens_restrictToChart
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    Nonempty ((Scheme.Modules.pullback W.ι).obj (restrictToChart B S hS X.2 F A) ≅
      restrictToChart B S hS X.2 F ((chartOpens B S hS A).obj W)) := by
  obtain ⟨e⟩ := nonempty_pullback_restrictToChartScheme B S hS X F hF
    (chartOpensHom B S hS X A W)
  exact ⟨eqToIso (congrArg (fun N => (Scheme.Modules.pullback W.ι).obj N)
      (restrictToChart_eq_restrictToChartScheme B S hS X.2 F A)) ≪≫ e ≪≫
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 F
      ((chartOpens B S hS A).obj W)).symm⟩

/-- The restriction of the chart restriction to the slice of the Zariski site of the chart at a
Zariski open `W`, carried to the open subscheme by `AlgebraicGeometry.Scheme.Modules.overEquiv`,
is the chart restriction at the étale chart `W` cuts out. -/
theorem nonempty_over_restrictToChart_chartOpens
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    Nonempty ((Scheme.Modules.overEquiv W).functor.obj
        ((restrictToChart B S hS X.2 F A).over W) ≅
      restrictToChart B S hS X.2 F ((chartOpens B S hS A).obj W)) := by
  obtain ⟨e⟩ := nonempty_pullback_opens_restrictToChart B S hS X F hF A W
  exact ⟨(Scheme.Modules.overFunctorEquiv W).app (restrictToChart B S hS X.2 F A) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app
      (restrictToChart B S hS X.2 F A) ≪≫ e⟩

/-- The restriction of the chart restriction to the open subspace `W` is the chart restriction
at the étale chart `W` cuts out. -/
theorem nonempty_restrictMod_restrictToChart_chartOpens
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    Nonempty (_root_.LocallyFreeRank.restrictMod (TopCat.of ↥(chartScheme A)) W
        (chartScheme A).ringCatSheaf (restrictToChart B S hS X.2 F A) ≅
      restrictToChart B S hS X.2 F ((chartOpens B S hS A).obj W)) := by
  obtain ⟨e⟩ := nonempty_over_restrictToChart_chartOpens B S hS X F hF A W
  exact ⟨(_root_.LocallyFreeRank.restrictModIsoOver (TopCat.of ↥(chartScheme A)) W
    (chartScheme A).ringCatSheaf (restrictToChart B S hS X.2 F A)).symm ≪≫ e⟩

/-- At a Zariski open `W` of the chart of a small étale neighbourhood containing the chosen
point, the restriction of the chart restriction to the slice at `W`, carried to the open
subscheme, is the chart restriction at the chart of
`AlgebraicGeometry.Space.chartOpenNeighborhood`. -/
theorem nonempty_over_restrictToChart_chartOpenNeighborhood
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
    (W : (chartScheme N.chart).Opens) (hw : chartPoint B S hS X.1 N ∈ W) :
    Nonempty ((Scheme.Modules.overEquiv W).functor.obj
        ((restrictToChart B S hS X.2 F N.chart).over W) ≅
      restrictToChart B S hS X.2 F (chartOpenNeighborhood B S hS N W hw).chart) :=
  nonempty_over_restrictToChart_chartOpens B S hS X F hF N.chart W

end AlgebraicGeometry.Space

end
