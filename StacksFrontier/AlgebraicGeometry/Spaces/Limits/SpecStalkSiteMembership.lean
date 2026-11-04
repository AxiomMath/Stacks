module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The site contains the spectrum of a stalk, and the opens of its objects

Stating Stacks 0E91 the way the tag states it — over a scheme `S`, a retrocompact open
`U ⊆ S` and a point `s` outside `U` — requires producing objects of the big fppf site from that
geometry: the affine open neighbourhoods `W` of `s`, the intersections `W ∩ U`, the spectrum
`Spec 𝒪_{S,s}` of the local ring, and the open `V = Spec 𝒪_{S,s} ∩ U` of it. This file collects
the membership facts, so that none of them has to be carried as a hypothesis of the tag.

All of them reduce to size bounds, because `AlgebraicGeometry.BigFppfSite.Contains X` is by
definition `X.size < B.cutoff`. The opens are Stacks 000R (3), already available. The spectrum of
the stalk is Stacks 000R (9) applied to the bound `#𝒪_{X,x} ≤ size X` of
`AlgebraicGeometry.Scheme.mk_stalk_le_size`; this library already had that argument, but only for
a point of an object of the site, in
`AlgebraicGeometry.BigFppfSite.contains_Spec_stalk`. The proof uses nothing about the object
beyond its size bound, so it is restated here for a bare scheme contained in the site, which is
the form the geometry of Stacks 0E91 presents.

Note what is *not* needed: no cofinality bound on an index type. Routing the membership of
`Spec 𝒪_{S,s}` through a limit of affine schemes would need one, because bounding the size of a
limit needs a bound on the number of stages; bounding the cardinality of a stalk directly does
not.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_Spec_stalk_of_contains`: the spectrum of a stalk of a
  scheme contained in the site is contained in the site.
* `AlgebraicGeometry.BigFppfSite.contains_Spec_stalk_opens`: and so is any open of it.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- **The spectrum of a stalk of a scheme contained in a big fppf site is contained in that
site.** This is `AlgebraicGeometry.BigFppfSite.contains_Spec_stalk` for a bare scheme with a size
bound rather than for a point of an object of the site; that proof uses nothing about the object
beyond its size bound.

It is Stacks 000R (9) applied to `AlgebraicGeometry.Scheme.mk_stalk_le_size`: a stalk is covered
by the sections over the affine opens through the point, so its cardinality is bounded by the
size of the scheme. No cofinality hypothesis enters, in contrast with the route through a limit
of affine neighbourhoods. -/
theorem contains_Spec_stalk_of_contains (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (x : X) : B.Contains (Spec (X.presheaf.stalk x)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hX
    ((Scheme.mk_stalk_le_size X x).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- **An open of the spectrum of a stalk of a scheme contained in a big fppf site is contained
in that site.** This is the object the tag calls `V = Spec 𝒪_{S,s} ∩ U`. -/
theorem contains_Spec_stalk_opens (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
    (x : X) (V : (Spec (X.presheaf.stalk x)).Opens) : B.Contains (↑V : Scheme.{u}) :=
  B.contains_coe_opens (B.contains_Spec_stalk_of_contains hX x) V

end AlgebraicGeometry.BigFppfSite

end
