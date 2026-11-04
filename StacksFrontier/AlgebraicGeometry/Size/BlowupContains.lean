module

public import StacksFrontier.AlgebraicGeometry.Size.Blowup
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Blowups belong to a big fppf site whose base does

`AlgebraicGeometry.BigFppfSite.Contains X` is `X.size < B.cutoff`, so the size bounds of
`StacksFrontier/AlgebraicGeometry/Size/Blowup.lean` say at once that a blowup of a scheme
belonging to a big fppf site again belongs to it, in any centre whatsoever: the blowup is no
larger than the scheme it is a blowup of.

This is the form the size side conditions of Stacks 085Q ask for.  Those conditions name the
relative `Proj`s of `Stacks.Blowup.reesSituation` of three sheaves of ideals — on an étale
chart of an algebraic space, on the relation of the chart, and on the scheme of composable
pairs — and each of those three schemes is an object of the site, so
`AlgebraicGeometry.BigFppfSite.contains_relativeProj_reesSituation` applies to each with no
further hypothesis.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_blowUp`: `B.Contains (blowUp ℐ)` whenever
  `B.Contains X`.
* `AlgebraicGeometry.BigFppfSite.contains_relativeProj_reesSituation`: the same for the
  relative `Proj` of `Stacks.Blowup.reesSituation`.

## Implementation notes

`StacksFrontier/AlgebraicGeometry/Topologies/Fppf.lean` imports the cardinality layer, so this
file — which goes the other way, from the layer to the site — is a leaf of it rather than part
of it.  It is kept in the same directory as the bound it applies because it says nothing beyond
unfolding `AlgebraicGeometry.BigFppfSite.Contains`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- **A blowup of a scheme contained in a big fppf site is contained in it**, in any
quasi-coherent centre: by `AlgebraicGeometry.Scheme.size_blowUp_le` the blowup is no larger
than its base, and `B.Contains` is a bound on the size. -/
theorem contains_blowUp (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
    (ℐ : X.IdealSheafData) : B.Contains (blowUp ℐ) :=
  lt_of_le_of_lt (Scheme.size_blowUp_le ℐ) hX

/-- **The relative `Proj` of the Rees algebra of a quasi-coherent sheaf of ideals on a scheme
contained in a big fppf site is contained in it.**  This is
`AlgebraicGeometry.BigFppfSite.contains_blowUp` for the explicitly built Rees algebra
`Stacks.Blowup.reesSituation`, which the blowup of an algebraic space is constructed from. -/
theorem contains_relativeProj_reesSituation (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (ℐ : X.IdealSheafData) :
    B.Contains (Stacks.Blowup.reesSituation ℐ).relativeProj :=
  lt_of_le_of_lt (Stacks.Blowup.size_relativeProj_reesSituation_le ℐ) hX

end AlgebraicGeometry.BigFppfSite

end
