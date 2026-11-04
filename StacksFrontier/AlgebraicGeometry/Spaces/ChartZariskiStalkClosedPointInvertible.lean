module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible

/-!
# The global sections on a chart of an invertible module at a point with no proper neighbourhood

Let `ℒ` be an invertible `𝒪_X`-module on an algebraic space `X`, let `x̄` be a geometric point
and let `V` be a small étale neighbourhood of `x̄` whose chart carries a point with no proper
open neighbourhood — the spectrum of a local ring and its closed point.  Then the sections of
the restriction of `ℒ` to the chart over the *whole* chart are free of rank one over the ring
of global regular functions on it.

The Zariski stalk of the chart restriction is free of rank one over the local ring of the chart
by `AlgebraicGeometry.Space.nonempty_linearEquiv_chartZariskiModuleStalk_of_isInvertibleModule`,
and at such a point the stalk is the module of global sections and the local ring the ring of
global functions, by
`AlgebraicGeometry.Space.chartZariskiModuleStalkTopLinearEquiv`.

## Main results

* `AlgebraicGeometry.Space.nonempty_linearEquiv_chartRestrictionTop_of_isInvertibleModule`:
  **the sections over the whole chart of the chart restriction of an invertible module are free
  of rank one.**

## Implementation notes

This is kept apart from
`StacksFrontier/AlgebraicGeometry/Spaces/ChartZariskiStalkClosedPoint.lean` because the proofs
there are about the two module structures Mathlib puts on the stalk of a presheaf of modules,
and the instances the invertibility file brings into scope resolve one of them differently;
the statement below is about the sections over `⊤` alone, where that does not arise.

No `stacks` attribute: this is a reading of
`AlgebraicGeometry.Space.nonempty_linearEquiv_chartZariskiModuleStalk_of_isInvertibleModule`,
which carries the Stacks 05VP citation, at a particular kind of point.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections over the whole chart of the chart restriction of an invertible module are
free of rank one**, at an étale scheme chart carrying a point with no proper open
neighbourhood — the spectrum of a local ring and its closed point. -/
theorem nonempty_linearEquiv_chartRestrictionTop_of_isInvertibleModule
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {y : GeometricPoint B S hS Y} (W : SmallEtaleNeighborhood y)
    (h : ∀ O : (chartScheme W.chart).Opens, chartPoint B S hS Y W ∈ O → O = ⊤)
    (L : Modules.{u, u} B S hS Y hY) (hL : IsInvertibleModule ⟨Y, hY⟩ L) :
    Nonempty (↥((chartRestrictionPresheafOfModules B S hS hY W L).obj (op ⊤)) ≃ₗ[
      Γ(chartScheme W.chart, ⊤)] Γ(chartScheme W.chart, ⊤)) :=
  (nonempty_linearEquiv_chartZariskiModuleStalk_of_isInvertibleModule B S hS hY W L hL).map
    (chartZariskiModuleStalkTopLinearEquiv B S hS hY W L h)

end AlgebraicGeometry.Space

end
