module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectFullyFaithfulHeld

/-!
# The reindexed situations of Stacks 0DKW are limits of schemes

`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectFullyFaithful_of_homDescent`
derives clauses (4) and (5) of Stacks 0DKW from Stacks 0DKV applied to the situation reindexed
at a later stage, `AlgebraicGeometry.Space.RelativeDescentSituation.atStage`, and carries as
`hstages` the fact that those reindexed situations are again limits of schemes on affine charts
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimitAtStages`).  The situation
`atStage i` is, field by field, the base's
`AlgebraicGeometry.Space.RelativeDescentSituation.reindex i`, so `hstages` is the base's
`AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_reindex`.

## Main results

* `RelativeDescentSituation.atStage_eq_reindex`: `atStage i = reindex i`.
* `RelativeDescentSituation.isSchemeLimitAtStages`: `hstages` holds.
* `RelativeDescentSituation.relativelyPerfectFullyFaithful_of_homDescentOfPseudoCoherent`:
  clauses (4) and (5) of Stacks 0DKW from Stacks 0DKV alone.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- The situation moved to a later stage `i` is the base's reindexing at `i`. -/
theorem atStage_eq_reindex (i : D.LaterIndex) : D.atStage i = D.reindex i :=
  rfl

/-- If `D` is a limit of schemes on affine charts, then so is the situation reindexed at each
later stage. -/
theorem isSchemeLimitAtStages : D.IsSchemeLimitAtStages :=
  fun hD i => D.isSchemeLimit_reindex i hD

/-- Clauses (4) and (5) of Stacks 0DKW (fullness and faithfulness) hold for `D`, given the
descent of morphisms of pseudo-coherent objects of Stacks 0DKV. -/
theorem relativelyPerfectFullyFaithful_of_homDescentOfPseudoCoherent
    (h0DKV : HomDescentOfPseudoCoherent B S hS hZ I) : D.RelativelyPerfectFullyFaithful :=
  D.relativelyPerfectFullyFaithful_of_homDescent h0DKV D.isSchemeLimitAtStages

end AlgebraicGeometry.Space.RelativeDescentSituation

end
