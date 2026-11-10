module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionSliceCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitEq

/-!
# The two dictionary squares of Stacks 03LY, unconditionally

The chart-to-slice dictionary for modules is compatible with the composition comparisons on the
two sides; that is the pair of squares
`AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare` and
`AlgebraicGeometry.Space.ChartModuleRestrictionSliceSquare`.  Both are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceCoherence.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionSliceCoherence.lean` from one
hypothesis: the coherence of the composition comparison of Stacks 03LU against the identification
of Stacks 03LW, for a composable pair of étale *representable* morphisms of algebraic spaces.

That hypothesis is now a theorem.
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` needs only that the two
adjunctions of étale restriction along the composite have the same unit, and
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit` proves exactly that, for a
composable pair of étale morphisms and with no further hypothesis.  So this file discharges the
hypothesis and restates both squares, and the cocycle condition they give, with no hypothesis at
all.

Representability is available where the squares are used: the morphism of algebraic spaces
represented by a morphism of charts is relatively representable
(`AlgebraicGeometry.Space.relativelyRepresentable_chartMap`), so is the structure morphism of a
chart (`AlgebraicGeometry.Space.relativelyRepresentable_chartToSpace`), and the only pairs the two
squares feed the hypothesis are pairs of those.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_representable`:
  the coherence of Stacks 03LU against Stacks 03LW for étale representable morphisms, with no
  hypothesis.
* `AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp_unconditional` and
  `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_comp_unconditional`: **the two
  dictionary squares of Stacks 03LY.**
* `AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily_unconditional`:
  the cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing datum
  for modules.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The coherence of Stacks 03LU against Stacks 03LW for étale representable morphisms.**  The
composition comparison of the pullbacks of modules followed by the identification of the pullback
along the composite with étale restriction is the identification in each factor followed by the
strict composition of the étale restrictions.

This is `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` with its
hypothesis discharged by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`, which needs no relative
representability, so the statement carries no representability hypothesis. -/
theorem modulePullbackCompIso_hom_comp_etaleRestriction_of_representable
    {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) :
    (modulePullbackCompIso B S hS h g).hom ≫
        (modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg).hom =
      Functor.whiskerLeft (modulePullback B S hS g)
          (modulePullbackIsoEtaleModulePullback B S hS h hh).hom ≫
        Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).hom
            (etaleModulePullback.{u, u} B S hS h hh) ≫
          (etaleModulePullbackComp B S hS h g hh hg hhg).hom :=
  modulePullbackCompIso_hom_comp_etaleRestriction B S hS h g hh hg hhg
    (etaleModulePullbackCompAdjunction_unit B S hS h g hh hg hhg)

variable (X : AlgebraicSpaces B S hS)

/-- **The first dictionary square of Stacks 03LY**, with no hypothesis: the chart-to-slice
dictionary for modules carries the chartwise composition comparison
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp` to the slice-side one
`AlgebraicGeometry.Space.overMapCompInvApp`.

This is `AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp` with its coherence
hypothesis discharged by
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_representable`. -/
theorem chartModuleInverseImageSliceApp_comp_unconditional
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartModuleInverseImage B S hS X g).map
          (chartModuleInverseImageSliceApp B S hS X f T) ≫
        chartModuleInverseImageSliceApp B S hS X g
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
      chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj T) ≫
        chartModuleInverseImageSliceApp B S hS X (g ≫ f) T ≫
          (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T) :=
  chartModuleInverseImageSliceApp_comp B S hS X
    (fun h' g' hh' hg' hhg' _ _ _ ↦
      modulePullbackCompIso_hom_comp_etaleRestriction_of_representable B S hS h' g' hh' hg' hhg')
    f g T

/-- **The second dictionary square of Stacks 03LY**, with no hypothesis: the dictionary carries
`AlgebraicGeometry.Space.chartModuleRestrictionComp` to `SheafOfModules.overFunctorMap`.

This is `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_comp` with its coherence
hypothesis discharged. -/
theorem chartModuleRestrictionSliceIso_comp_unconditional
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleInverseImage B S hS X f).map
          ((chartModuleRestrictionSliceIso B S hS X U).hom.app F) ≫
        chartModuleInverseImageSliceApp B S hS X f
            ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ≫
          (chartModuleSliceReindex B S hS X V).map
            ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F) =
      (chartModuleRestrictionComp B S hS X f).hom.app F ≫
        (chartModuleRestrictionSliceIso B S hS X V).hom.app F :=
  chartModuleRestrictionSliceIso_comp B S hS X
    (fun h' g' hh' hg' hhg' _ _ _ ↦
      modulePullbackCompIso_hom_comp_etaleRestriction_of_representable B S hS h' g' hh' hg' hhg')
    f F

/-- **The cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing
datum for modules**, with no hypothesis: the first dictionary square
`AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp_unconditional` handed as an explicit
`∀` to `AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square`,
as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleGlueingEquivalence.lean` require. -/
theorem isChartModuleCocycle_sliceToChartModuleTransitionFamily_unconditional
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)) :
    IsChartModuleCocycle B S hS X (sliceToChartModuleFamily B S hS X D)
      (sliceToChartModuleTransitionFamily B S hS X D) :=
  isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square B S hS X D
    (fun f g T ↦ chartModuleInverseImageSliceApp_comp_unconditional B S hS X f g T)

end AlgebraicGeometry.Space

end
