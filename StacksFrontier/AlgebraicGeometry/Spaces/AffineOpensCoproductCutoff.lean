module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff

/-!
# The coproduct of all the affine opens of a scheme of a big fppf site

`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` keeps a coproduct of schemes of a
big fppf site inside the site when the index type is smaller than the cofinality of the
cutoff, and that hypothesis is unavoidable in general: the cutoff need not be regular, so a
supremum of fewer than `B.cutoff` sizes each below `B.cutoff` can equal `B.cutoff`.

For one family it is not needed at all. The affine opens of a scheme `X` are at most
`X.size` in number (`AlgebraicGeometry.Scheme.mk_affineOpens_le_size`) and each of them is
an open subscheme, hence of size at most `X.size`
(`AlgebraicGeometry.Scheme.size_coe_opens_le`): the sizes of the members are bounded by the
single cardinal `X.size` rather than merely each below the cutoff, so the open-cover bound
of Stacks 000Q puts the coproduct at size at most `X.size` and no supremum has to be
estimated. The coproduct of *all* the affine opens of a scheme of the site is therefore
again a scheme of the site, whatever the cofinality of the cutoff.

This is the object over which a sheaf on a site containing it sees all of those affine opens
at once: the component immersions cover it, so its sections restrict onto the sections over
each affine open of `X`, and a bound on the former bounds all of the latter together.

## Main results

* `AlgebraicGeometry.schemeSize_sigma_affineOpens_le`: the coproduct of all the affine opens
  of `X` has size at most `X.size`.
* `AlgebraicGeometry.BigFppfSite.contains_sigma_affineOpens`: a big fppf site contains that
  coproduct for every scheme it contains.

## References

* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The coproduct of all the affine opens of a scheme has size at most that of the
scheme.** Both inputs of the open-cover bound are `X.size` itself: the affine opens are at
most `X.size` in number, and each is an open subscheme of `X`. -/
theorem schemeSize_sigma_affineOpens_le (X : Scheme.{u}) :
    Scheme.size (∐ fun V : X.affineOpens => (V.1 : Scheme.{u})) ≤ X.size :=
  schemeSize_coproduct_le _ X.size X.aleph0_le_size X.mk_affineOpens_le_size
    fun V => X.size_coe_opens_le V.1

namespace BigFppfSite

/-- **A big fppf site contains the coproduct of all the affine opens of any scheme it
contains.** Unlike `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` this needs no
hypothesis relating the index type to the cofinality of the cutoff, the sizes of the members
being bounded by the size of `X` itself. -/
theorem contains_sigma_affineOpens (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) :
    B.Contains (∐ fun V : X.affineOpens => (V.1 : Scheme.{u})) :=
  (schemeSize_sigma_affineOpens_le X).trans_lt hX

end BigFppfSite

end AlgebraicGeometry

end
