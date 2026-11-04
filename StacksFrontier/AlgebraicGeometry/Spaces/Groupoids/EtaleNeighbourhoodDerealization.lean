module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionArrowSections

/-!
# The separated étale neighbourhood of a de-realized étale neighbourhood

`Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable` turns an algebraic space
which is étale over the object space of the realization of a groupoid scheme, and whose underlying
presheaf is representable, into a scheme over `S` which is étale over the object scheme, together
with the comparison isomorphism identifying the two.  Stacks 04RY produces such a neighbourhood
and asserts in addition that it is *separated* over the object space; this file carries that
assertion across the same comparison, so that the de-realized morphism of schemes is separated as
well as étale.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isSeparated_of_isSeparated_realizationIso`: the de-realized
  morphism of schemes is separated when the morphism of algebraic spaces it came from is.

## Implementation notes

Separatedness of a morphism of schemes over `S` between two schemes which the site contains is
separatedness of the morphism of algebraic spaces it represents
(`AlgebraicGeometry.Space.isSeparated_schemeSpaceMap_iff`), and the represented morphism is the
given one precomposed with the comparison isomorphism.  An isomorphism of algebraic spaces is
separated and separatedness is stable under composition, which is
`AlgebraicGeometry.Space.isSeparated_of_isIso` and
`AlgebraicGeometry.Space.isSeparated_comp`.

## References

* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
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

include he in
/-- **A de-realized étale neighbourhood of the object scheme is separated when the morphism of
algebraic spaces it came from is.** -/
theorem isSeparated_of_isSeparated_realizationIso
    (hsep : Space.IsSeparated C S hS g.hom) : AlgebraicGeometry.IsSeparated p.left := by
  rw [← isSeparated_schemeSpaceMap_iff C hS hX hU p]
  have hhom : (siteSchemeSpaceMap C hS hX hU p).hom = e.hom ≫ g.hom := he.symm
  rw [hhom]
  exact Space.isSeparated_comp C S hS e.hom g.hom
    (Space.isSeparated_of_isIso C S hS e.hom) hsep

end Stacks.Groupoids.GroupoidScheme

end
