module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfBigFppf

/-!
# A big étale site of algebraic spaces over a big fppf site of schemes

The étale covering families of the algebraic spaces over a scheme `S` contained in a big fppf
site `B` of schemes satisfy the site axioms (Stacks 041F), so Stacks 000X bounds them by a
cardinal. This gives a big étale site of algebraic spaces over `S` whose auxiliary big fppf site
of schemes is `B` itself, so that its algebraic spaces are the algebraic spaces over `S` built on
`B`, on the nose.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.bigEtaleSpaceSite`: the big étale site of algebraic spaces over
  `S` with auxiliary big fppf site `B`, and with big étale site of schemes
  `AlgebraicGeometry.bigEtaleSiteOfFppfSite B`.

## Implementation notes

`AlgebraicGeometry.BigFppfSpaceSite.bigEtaleSpaceSite` and
`AlgebraicGeometry.BigPHSpaceSite.bigEtaleSpaceSite` make the same construction starting from a big
fppf site, respectively a big ph site, of algebraic spaces; it only uses the big fppf site of
schemes, which is all that is given here. The definition is reducible: the identifications of the
small étale topoi of `B.bigEtaleSpaceSite S hS` with those built on `B` are then definitional
equalities which the elaborator checks quickly, which the comparisons of Stacks 0DGU with the
small étale site of a simplicial algebraic space need.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- **A big étale site of algebraic spaces over a big fppf site of schemes**: its auxiliary big
fppf site of schemes is `B`, its big étale site of schemes is the one on the same schemes, and it
has no initial coverings and the covering bound of Stacks 000X. -/
abbrev bigEtaleSpaceSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    BigEtaleSpaceSite S :=
  let h := exists_covBounded_isSite_of_univ.{_, _, u + 2}
    (Space.IsEtaleCoveringFamily B S hS)
    (Space.isSite_isEtaleCoveringFamily B S hS) ∅ (by intro U hU; cases hU)
  { schemeSite := bigEtaleSiteOfFppfSite B
    scheme_mem := hS
    fppfSite := B
    fppf_mem := hS
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_etale := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

/-- The auxiliary big fppf site of schemes of `B.bigEtaleSpaceSite S hS` is `B`. -/
theorem bigEtaleSpaceSite_fppfSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (B.bigEtaleSpaceSite S hS).fppfSite = B :=
  rfl

end AlgebraicGeometry.BigFppfSite

end
