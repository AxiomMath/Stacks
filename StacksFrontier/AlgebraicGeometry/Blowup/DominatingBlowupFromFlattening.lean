module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme

/-!
# A proper modification is dominated by an admissible blowup

[Stacks, Tag 081T] is proved in `StacksFrontier/AlgebraicGeometry/Blowup/DominatedByBlowup.lean`
from the two results its source cites, [Stacks, Tag 080Y] and [Stacks, Tag 081S]. Both are now
available on their own hypotheses: tag 080Y as `AlgebraicGeometry.cartierBoundaryReduction` and
tag 081S as `AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`. Here
tag 081T is restated with both of them supplied.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_affineCharts`: tag 081T with
  `AlgebraicGeometry.AffineChartFlatteningCentre` as an extra input, the affine case of the
  flatness half of [Stacks, Tag 0815] with that tag's hypotheses (2)-(5) deleted. No tag: that
  predicate is false in general.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_affineCase`:
  **[Stacks, Tag 081T]**, a proper morphism which is an isomorphism over a quasi-compact open of
  a quasi-compact quasi-separated base is dominated by an admissible blowup, under exactly the
  source's hypotheses. This is where the tag is registered.

## Implementation notes

The affine case of the flatness assertion of [Stacks, Tag 0815] that the chain
0815 → 081R → 081S → 081T runs on is
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, proved from
[Stacks, Tag 0811]. The form taking `AlgebraicGeometry.AffineChartFlatteningCentre` is kept
beside it, for the sake of the reduction it isolates; that predicate is false in general, and
for the datum of this tag it is produced by
`AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase` out of the tag's own hypothesis
that `f` be an isomorphism over `U`.

## References

* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 081T.** Let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated, and let `U ⊆ S` be a quasi-compact open such that `f` is an isomorphism over
`U`. Then there is a `U`-admissible blowup `b : S' ⟶ S` which dominates `X`: a morphism
`g : S' ⟶ X` with `g ≫ f = b`.

Both results the source cites are now supplied: [Stacks, Tag 080Y] by
`AlgebraicGeometry.cartierBoundaryReduction` and [Stacks, Tag 081S] by
`AlgebraicGeometry.strictTransformOpenImmersion_of_affineCharts`.

This tag is NOT registered on this declaration: the extra input
`AffineChartFlatteningCentre` is the affine case of tag 0815 with that tag's hypotheses
(2)-(5) deleted, which is false in general. The tag sits on
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_affineCase` below.
-/
theorem exists_isAdmissibleBlowup_dominating_of_affineCharts (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    [IsIso (f ∣_ U)] (H : AffineChartFlatteningCentre f X.unitModule U) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ g : S' ⟶ X, g ≫ f = b :=
  exists_isAdmissibleBlowup_dominating_of_isCompact f U hU
    (strictTransformOpenImmersion_of_affineCharts f U hU H)

/-- **Stacks Project, Tag 081T.** Let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated, and let `U ⊆ S` be a quasi-compact open such that `f` is an isomorphism over
`U`. Then there is a `U`-admissible blowup `b : S' ⟶ S` which dominates `X`: a morphism
`g : S' ⟶ X` with `g ≫ f = b`.

The hypotheses are exactly the source's. Both results the source cites are supplied by proved
declarations: [Stacks, Tag 080Y] by `AlgebraicGeometry.cartierBoundaryReduction` and
[Stacks, Tag 081S] by `AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`,
each of which stands on its own hypotheses alone. -/
@[stacks 081T "the conclusion in full, under exactly the source's hypotheses: the cited \
[Stacks, Tag 080Y] is supplied by `AlgebraicGeometry.cartierBoundaryReduction` and the cited \
[Stacks, Tag 081S] by `AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`, \
each of which stands on its own hypotheses alone"]
theorem exists_isAdmissibleBlowup_dominating_of_affineCase (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    [IsIso (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ g : S' ⟶ X, g ≫ f = b :=
  exists_isAdmissibleBlowup_dominating_of_isCompact f U hU
    (strictTransformOpenImmersion_of_isIso_morphismRestrict f U hU)

end AlgebraicGeometry

end
