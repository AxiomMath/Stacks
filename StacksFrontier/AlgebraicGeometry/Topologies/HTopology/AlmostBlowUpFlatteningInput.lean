module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningFlatModel
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion

/-!
# The flattening input of the converse direction of Stacks tag 0EVF

`AlgebraicGeometry.FinitePresentationHasAlmostBlowUpFlattening` is the affine-base case of Stacks
tag 0EVC, carried as an unproved `Prop` in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion` because that is
the single geometric input the converse direction of Stacks tag 0EVF is missing.

It is no longer out of reach of the 0EVC cluster. An affine scheme is quasi-compact and
quasi-separated, and `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat_pullback` proves tag
0EVC under exactly the tag's hypotheses over such a base, carrying only the affine case of the
flatness assertion of Stacks tag 0815. So the flattening input reduces to that affine case alone,
and the reduction is recorded here.

## Main results

* `AlgebraicGeometry.finitePresentationHasAlmostBlowUpFlattening_of_noetherianAffineChart`: the
  flattening input of the converse direction of Stacks tag 0EVF follows from
  `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre`, the affine case of the flatness
  assertion of Stacks tag 0815.

## Implementation notes

This does not close the converse direction of Stacks tag 0EVF, and it carries no `@[stacks]`
attribute: it replaces one unproved input by another, strictly smaller one. What it removes is the
*distance* between them. The docstring of
`AlgebraicGeometry.FinitePresentationHasAlmostBlowUpFlattening` assumes the form
of tag 0EVC over a locally Noetherian base, and reasons from that to the conclusion that
"an affine scheme is neither locally Noetherian nor reachable from the Noetherian case, so neither
form gives the statement below"; absolute Noetherian approximation
(`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_affineChartFlatteningCentre_model`) and the
descent of the flatness over the open
(`AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation_of_flat`) between them remove
both obstructions, and that paragraph has been corrected accordingly.

What remains of the converse direction of tag 0EVF is therefore the three steps the source takes
*after* tag 0EVC, none of which is in this development: the bijectivity of `F(T') ⟶ F(T)` for a
finite-presentation thickening, the extension of condition (3) from an affine base to an
arbitrary one, and the induction along the generic flatness stratification — the stratification
itself being available as
`AlgebraicGeometry.finitePresentationHasFlatStratification` (Stacks tag 0H3Z).

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The affine-base case of Stacks tag 0EVC, from the affine case of Stacks tag 0815.** The
flattening input of the converse direction of Stacks tag 0EVF,
`AlgebraicGeometry.FinitePresentationHasAlmostBlowUpFlattening`, follows from
`AlgebraicGeometry.NoetherianAffineChartFlatteningCentre`.

An affine scheme is quasi-compact and quasi-separated, so
`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat_pullback` — tag 0EVC under the tag's own
hypotheses, by absolute Noetherian approximation together with the descent of the flatness over
the open — applies to it with nothing further assumed. -/
theorem finitePresentationHasAlmostBlowUpFlattening_of_noetherianAffineChart
    (H : NoetherianAffineChartFlatteningCentre.{u}) :
    FinitePresentationHasAlmostBlowUpFlattening.{u} := fun f hf V hV hVflat ↦
  hasFlatAlmostBlowUpSquarePair_of_flat_pullback f hf V hV hVflat H

end AlgebraicGeometry

end
