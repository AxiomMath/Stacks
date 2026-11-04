module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineOverlaps
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModule

/-!
# The slice of the small étale site at a chart has its finite limits computed by schemes

`AlgebraicGeometry.Space.SmallEtale.sliceToOver` reads the slice of the small étale site of an
algebraic space `F` at an étale chart `X` as a category of schemes over the scheme underlying
`X`.  This file shows that this functor preserves finite limits: the iterated fibre products of a
family of charts over `X` are carried to the iterated fibre products of the underlying schemes
over the underlying scheme. This is condition (2) of [Stacks, Tag 00WV] for the projection.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.hasFiniteLimits_over_chartScheme`: the schemes over the
  chart's scheme have finite limits.
* `AlgebraicGeometry.Space.SmallEtale.preservesTerminal_sliceToOver`: the projection carries the
  terminal object of the slice, which is the chart itself, to the terminal object of the schemes
  over the chart's scheme, which is that scheme.
* `AlgebraicGeometry.Space.SmallEtale.preservesFiniteLimits_sliceToOver`: the projection
  preserves finite limits.
* `AlgebraicGeometry.Space.hasFiniteLimits_overChart`: the slice of the small étale site at a
  chart has finite limits.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : SmallEtale B S hS F)

/-- The schemes over the scheme underlying a chart have finite limits. -/
noncomputable instance hasFiniteLimits_over_chartScheme :
    HasFiniteLimits (Over (chartScheme X)) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The slice projection preserves the terminal object: the terminal object of the slice at `X`
is `X` itself, and the projection carries it to the identity of the chart's scheme, the terminal
object of the schemes over that scheme. -/
noncomputable instance preservesTerminal_sliceToOver :
    PreservesLimitsOfShape (Discrete.{0} PEmpty) (sliceToOver B S hS F X) := by
  refine CategoryTheory.Functor.preservesLimitsOfShape_pempty_of_isTerminal _
    (Over.mkIdTerminal (X := X)) ?_
  simpa [sliceToOver] using Over.mkIdTerminal (X := chartScheme X)

/-- The slice projection preserves finite limits.  In particular it carries the iterated
fibre products of a family of charts over `X` to the iterated fibre products of the underlying
schemes over the chart's scheme, which is condition (2) of [Stacks, Tag 00WV]. -/
noncomputable instance preservesFiniteLimits_sliceToOver :
    PreservesFiniteLimits (sliceToOver B S hS F X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The slice of the small étale site of an algebraic space at a chart has finite limits. -/
theorem hasFiniteLimits_overChart (U : SmallEtale B S hS F) :
    HasFiniteLimits (Over U) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end AlgebraicGeometry.Space

end
