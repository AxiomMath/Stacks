module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation

/-!
# The étale pullback to a chart space is the 04M0 reading of the restriction

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `W` be
an étale scheme chart of `X`.  There are two ways to read "the restriction of an `𝒪_X`-module to
`W`" as a module on the small étale site of the chart space of `W`:

* pull back along the structure morphism `chartSpace W ⟶ X`, which is étale, using the pullback
  of modules of Stacks 03LU — `AlgebraicGeometry.Space.etaleModulePullback`;
* restrict to the slice of the small étale site of `X` at `W` and reindex along the comparison
  equivalence of Stacks 04M0 — `AlgebraicGeometry.Space.chartSmallEtaleRestriction`.

The two agree on the nose.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePullbackChartToSpaceIso`: the two readings as an
  isomorphism.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_eq_chartSmallEtaleRestriction`: the
  étale pullback of an `𝒪_X`-module to a chart space is the 04M0 reading of its restriction to
  the chart.
* `AlgebraicGeometry.Space.isFinitePresentation_etaleModulePullback_chartToSpace_iff`: finite
  presentation of the pullback is finite presentation of the restriction to the slice.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The étale pullback of an `𝒪_X`-module to a chart space is the 04M0 reading of its
restriction to the chart.**  The pullback of Stacks 03LU along the structure morphism of an étale
scheme chart `W` of `X` and the reindexing along the comparison equivalence of Stacks 04M0 of the
restriction of the module to the slice at `W` are the same module on the small étale site of the
chart space of `W`. -/
theorem etaleModulePullback_chartToSpace_eq_chartSmallEtaleRestriction
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1) :
    (etaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj M =
      chartSmallEtaleRestriction B S hS X M W :=
  rfl

/-- The étale pullback of an `𝒪_X`-module to a chart space and the 04M0 reading of its
restriction to the chart are isomorphic. -/
noncomputable def etaleModulePullbackChartToSpaceIso
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1) :
    (etaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj M ≅
      chartSmallEtaleRestriction B S hS X M W :=
  eqToIso (etaleModulePullback_chartToSpace_eq_chartSmallEtaleRestriction B S hS X M W)

/-- **Finite presentation of the étale pullback to a chart space.**  The pullback of Stacks 03LU
of an `𝒪_X`-module along the structure morphism of an étale scheme chart `W` is of finite
presentation exactly when the restriction of the module to the slice of the small étale site at
`W` is. -/
theorem isFinitePresentation_etaleModulePullback_chartToSpace_iff
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1) :
    ((etaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).obj M).IsFinitePresentation ↔
      (M.over W).IsFinitePresentation :=
  isFinitePresentation_chartSmallEtaleRestriction_iff B S hS X M W

end AlgebraicGeometry.Space
