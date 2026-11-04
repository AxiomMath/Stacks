module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchIdentityArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# The étale-local-ring form of the reductions of Stacks 06E4

The first two reductions in the proof of [Stacks Project, Tag 06E4] bring geometric
unibranchness of the arrow space `R` of a groupoid in algebraic spaces over a field down to
geometric unibranchness of the arrow space of each restriction along an algebraically closed
field extension, at the point of its identity arrow
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_identityArrows`).

Geometric unibranchness at a point is condition (4) of Tag 06DK, and condition (5) there is
that the étale local ring at every geometric point above it has a unique minimal prime
(`AlgebraicGeometry.Space.HasUniqueMinimalPrimeAtGeometricPoints`).  Feeding the equivalence of
the two into the reductions puts the remaining content of Tag 06E4 where the source puts it:
in the minimal primes of the étale local rings `A = 𝒪_{R, e}` and
`C = 𝒪_{R ×_{s, U, t} R, (e, e)}`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_minimalPrimes`:
  the arrow space of a groupoid in algebraic spaces over a field is geometrically unibranch as
  soon as, for every algebraically closed extension of that field whose spectrum lies in the
  site, the étale local ring of the restricted arrow space at every geometric point above the
  identity arrow has a unique minimal prime.

## Implementation notes

The restricted arrow space is an algebraic space, which is what the equivalence of the five
conditions of Tag 06DK needs; the witness is the `ObjectProperty` component of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`.

No `@[stacks 06E4]` attribute is claimed: the hypothesis is the local computation of the last
two paragraphs of the source proof, which is the hard part of the tag.

## References

* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06DK](https://stacks.math.columbia.edu/tag/06DK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
  (structureMap : Spec (.of k) ⟶ S)
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

/-- **The reductions of Stacks 06E4, in terms of minimal primes of étale local rings.** Let `G`
be a groupoid in algebraic spaces whose object space is the spectrum of a field `k`.  Suppose
that for every algebraically closed field extension `k'/k` whose spectrum lies in the site, the
étale local ring of the restricted arrow space at every geometric point above the point of its
identity arrow has a unique minimal prime.  Then the arrow space of `G` is geometrically
unibranch.

This is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_identityArrows`
with its hypothesis replaced by condition (5) of Tag 06DK in place of condition (4).

No `@[stacks 06E4]` attribute is claimed: the hypothesis is the local computation, which is the
hard part of the tag. -/
theorem isGeometricallyUnibranch_arrows_of_minimalPrimes
    (hres : ∀ (k' : Type u) (_ : Field k') (_ : IsAlgClosed k') (i : k →+* k')
      (hk' : C.Contains (Spec (.of k'))),
      Space.HasUniqueMinimalPrimeAtGeometricPoints C S hS
        (restrictionArrows G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
        (restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i)) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj := by
  refine isGeometricallyUnibranch_arrows_of_identityArrows C hS hk structureMap G hU ?_
  intro k' field' alg' i hk'
  exact ((Space.uniqueBranch_tfae C S hS
    (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
    (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).property
    (restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i)).out 5 4).mp
    (hres k' field' alg' i hk')

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
