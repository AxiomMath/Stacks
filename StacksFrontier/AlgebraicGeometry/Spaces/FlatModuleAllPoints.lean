module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence

/-!
# Flatness over the target is flatness over the target at every point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be a quasi-coherent `𝒪_X`-module.  Stacks 05VV defines *flat over* `Y` as the conditions of
Stacks 05VU holding at every point of `|X|`; in this development
`AlgebraicGeometry.Space.IsFlatOver` is instead the chartwise form on *every* commuting square
of étale scheme charts, and `AlgebraicGeometry.Space.IsFlatOverAtPoint` is the pointwise form,
which quantifies over *some* square.  This file closes the loop between the two: the global
predicate holds exactly when the pointwise one holds at every point of `|X|`, so `IsFlatOver`
really is the all-`x` version of `IsFlatOverAtPoint`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_of_forall_isFlatOverAtPoint`: flatness over `Y` at every
  point of `|X|` gives flatness over `Y`.
* `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtPoint`: **Stacks 05VV**, the two
  readings agree.

## Implementation notes

Only the direction proved here needs quasi-coherence of `F`, and it needs it for a reason of
mathematics rather than of bookkeeping: `AlgebraicGeometry.Space.IsFlatOverAtPoint` asks the
ringed-space condition on *some* square of charts through the point while
`AlgebraicGeometry.Space.IsFlatOver` asks it on *every* square, so passing from the pointwise
hypothesis to the global conclusion is exactly the chart independence of Stacks 05VU — which is
false for a general `𝒪_X`-module and is proved there for a quasi-coherent one.  The input is
`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModulePointChartIndependence.lean`, itself a corollary
of the registered
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`.

The converse direction needs nothing: it is
`AlgebraicGeometry.Space.isFlatOverAtPoint_of_isFlatOver`, which reads the global condition at a
chart point, together with
`AlgebraicGeometry.Space.exists_chartDiagram_pointOfEtaleChart`, which says every point of `|X|`
is a chart point of some square.

This file lives downstream of `StacksFrontier/AlgebraicGeometry/Spaces/FlatModule.lean`, where both
predicates are defined, because the chart independence it rests on is itself downstream of that
file.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness over the target at every point gives flatness over the target.** For a
quasi-coherent `𝒪_X`-module `F`, if `F` is flat over `Y` at every point of `|X|` in the
some-chart sense of `AlgebraicGeometry.Space.IsFlatOverAtPoint`, then `F` is flat over `Y` in
the every-chart sense of `AlgebraicGeometry.Space.IsFlatOver`.

Quasi-coherence is a hypothesis of the mathematics here, not a convenience: the hypothesis
offers one square of charts through each point and the conclusion demands all of them, so this
is the chart independence of Stacks 05VU, which fails for a general `𝒪_X`-module. -/
theorem isFlatOver_of_forall_isFlatOverAtPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (h : ∀ x : points B S hS X.1, IsFlatOverAtPoint B S hS X.2 f.hom F x) :
    IsFlatOver B S hS X.2 f.hom F := fun d u =>
  (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u).mp
    (h (pointOfEtaleChart B S hS d.U u))

/-- **Stacks 05VV, the all-`x` characterisation.** For a quasi-coherent `𝒪_X`-module `F`,
flatness of `F` over `Y` in the every-chart sense of `AlgebraicGeometry.Space.IsFlatOver` holds
exactly when `F` is flat over `Y` at every point of `|X|` in the pointwise sense of
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, which is condition (1) of Stacks 05VU at that
point.  This is the form in which the source states the definition: `F` is flat over `Y` when
the equivalent conditions of Stacks 05VU hold at every point of `|X|`.

The forward direction holds for an arbitrary `𝒪_X`-module; quasi-coherence is what makes the
pointwise condition chart-independent and so is needed only for the converse. -/
@[stacks 05VV "the all-x characterisation, for a quasi-coherent module"]
theorem isFlatOver_iff_forall_isFlatOverAtPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    IsFlatOver B S hS X.2 f.hom F ↔
      ∀ x : points B S hS X.1, IsFlatOverAtPoint B S hS X.2 f.hom F x := by
  refine ⟨fun hflat x => ?_, isFlatOver_of_forall_isFlatOverAtPoint B S hS f F hF⟩
  obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 Y.2 f.hom x
  exact hu ▸ isFlatOverAtPoint_of_isFlatOver X.2 F hflat d u

end AlgebraicGeometry.Space

end
