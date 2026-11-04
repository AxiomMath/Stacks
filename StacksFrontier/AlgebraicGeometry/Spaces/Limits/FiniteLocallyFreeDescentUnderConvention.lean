module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention.BaseChangeToLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention.FrameDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention.ChartSystemDescent

/-!
# Finite locally free modules on a limit come from a stage, under the chapter's convention

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms satisfying the convention of
Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, with no bound on
the index.  Every finite locally free `𝒪_X`-module is the inverse image of a finite locally free
`𝒪_{Xᵢ}`-module for some `i`, as in Stacks 0D2X, part (1).

## Main results

* `exists_isFiniteLocallyFreeOnSite_stage_of_siteContainsBaseChangeLimits`: a finite locally free
  module on the limit is the inverse image of a finite locally free module on a stage.
-/
