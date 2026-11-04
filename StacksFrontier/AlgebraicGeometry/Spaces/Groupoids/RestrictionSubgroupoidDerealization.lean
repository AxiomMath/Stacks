module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionSubgroupoidClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionSubgroupoidTransport

/-!
# De-realizing an open finite subgroupoid of a restricted realization

An open finite subgroupoid of the restriction of the realization of a groupoid scheme, in the
sense of conditions (a) and (b) of Stacks 04RK for a groupoid in algebraic spaces, cuts an open
subscheme out of the arrow scheme of the restriction of the groupoid scheme, and that open
subscheme is an open finite subgroupoid in the sense of the same conditions read for a groupoid
scheme.

This is the comparison of the two readings of Stacks 04RK which the étale localization results
of Stacks 04RX, 04RY, 04RZ and 04S0 need: those tags produce the neighbourhood and the
subgroupoid in algebraic spaces, and state their conclusions about groupoid schemes.

## Main results

* `Stacks.Groupoids.GroupoidScheme.nonempty_openFiniteSubgroupoid_of_realization`: the
  de-realization, for an arbitrary groupoid scheme realizing the restriction.

## Implementation notes

The two halves are proved separately.  That the open subscheme is stable under the identity, the
inverse and the composition of the groupoid scheme is
`Stacks.Groupoids.GroupoidScheme.isArrowSubgroupoid_subgroupoidOpens`; that the restricted source
and target are finite is
`Stacks.Groupoids.GroupoidScheme.nonempty_openFiniteSubgroupoid_of_isArrowSubgroupoid`, which
carries the finiteness of the subgroupoid of the restricted realization across the comparison.
The groupoid axioms are then free, by
`Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid`: each of them is an equality of morphisms into
the object scheme or into the open subscheme of arrows, so it may be tested after composing with
the open immersion.

The conclusion is stated for an arbitrary
`AlgebraicGeometry.GroupoidScheme.Restriction`, not for the one built by
`AlgebraicGeometry.GroupoidScheme.restrict`, because the open subscheme is transported along the
equality of arrow schemes which that structure records.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) {X : Over S}
  (hX : C.Contains X.left) (p : X ⟶ G.objects) (U' : AlgebraicSpaces C S hS)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)
  (e : yoneda.obj (schemeSiteObject C hS hX) ≅ U'.obj)
  (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hX hU p))
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)

include he hA hB hRA in
/-- **De-realization of an open finite subgroupoid.**  An open finite subgroupoid of the
restriction of the realization of a groupoid scheme along a morphism out of an algebraic space
identified with a represented one gives an open finite subgroupoid of any groupoid scheme
realizing the restriction of the groupoid scheme along the corresponding morphism of schemes. -/
theorem nonempty_openFiniteSubgroupoid_of_realization
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid) :
    Nonempty (OpenFiniteSubgroupoid R'.groupoid) :=
  nonempty_openFiniteSubgroupoid_of_isArrowSubgroupoid G C hS hU hR hP hX p U' g e he hA hB hRA
    R' P (isArrowSubgroupoid_subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA R' P)

end Stacks.Groupoids.GroupoidScheme

end
