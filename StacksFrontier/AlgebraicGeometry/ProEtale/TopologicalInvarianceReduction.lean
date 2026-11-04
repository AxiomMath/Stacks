module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange

/-!
# Formal reductions for topological invariance of the small pro-étale topos

Stacks 09AB asserts that for an integral, universally injective and surjective morphism
`f : T ⟶ S` in a chosen big pro-étale site, the direct and inverse image functors of the
induced morphism `AlgebraicGeometry.ProEtale.smallProetaleMorphism` of small pro-étale topoi
are quasi-inverse *equivalences*.  Nothing in this file proves that.  What it records are the
two reductions of that statement which are formal, so that the mathematical remainder is
isolated and need only be proved once.

The first reduction is that the two halves of Stacks 09AB's conclusion are formally
interchangeable.  The inverse image and the direct image of a morphism of topoi are an adjoint
pair, and in an adjunction either adjoint is an equivalence as soon as the other one is.  Hence
only one of the two assertions of Stacks 09AB carries content.  Its remaining assertion, that
the two functors are *quasi-inverse*, is then `CategoryTheory.Adjunction.toEquivalence` of the
adjunction `f⁻¹ ⊣ f_*`, whose unit and counit are isomorphisms as soon as either functor is an
equivalence; no declaration is needed for it and none is added here.

The second reduction passes from the topos to the site.  The direct image of
`AlgebraicGeometry.ProEtale.smallProetaleMorphism` is by construction restriction of sheaves
along `AlgebraicGeometry.ProEtale.smallProetaleBaseChange`, so the comparison lemma makes it an
equivalence as soon as base change exhibits the small pro-étale site of `S` as a dense subsite
of the small pro-étale site of `T`.  That hypothesis is a sufficient site-level condition, not
a reformulation: it is stronger than the equivalence of topoi it produces.

## Main results

* `MorphismOfTopoi.isEquivalence_pushforward` — the direct image of a morphism of topoi is an
  equivalence as soon as its inverse image is; the converse is the instance
  `MorphismOfTopoi.isEquivalence_inverseImage`.
* `AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence_of_pushforward` and
  `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence_of_inverseImage` — the
  same statement for small pro-étale base change, in the binders of Stacks 09AB.
* `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence_of_isDenseSubsite` and
  `AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence_of_isDenseSubsite` — the
  site-level criterion.

## Implementation notes

* No declaration here carries a `@[stacks 09AB]` attribute, in any part-stringed form.  Each
  one either is a general statement about adjunctions, or carries as a hypothesis exactly the
  assertion that Stacks 09AB makes unconditionally; tagging such a form would record the tag as
  covered while the geometry is untouched.
* Stacks 09AB itself is proved in
  `StacksFrontier.AlgebraicGeometry.ProEtale.TopologicalInvariance`, and not by the dense-subsite
  criterion below.  The route taken there identifies the small pro-étale topos over an affine
  base with the topos of the affine ind-étale site, by
  `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction`, which is
  Stacks 098X for `AlgebraicGeometry.ProEtale.SmallProetale`, the small pro-étale site carved
  out of a chosen big site; that is the site on which the morphism of topoi of Stacks 09AB
  lives, so 098X applies to it directly.  The step which Stacks 09AB's own proof
  omits ("we omit the verification"), identifying the coverings of the two affine ind-étale
  sites, is carried out there.
* Two results that chapter 59 cites are still missing from this library, and are carried as
  explicit hypotheses of the statements there: essential surjectivity of base change on small
  étale sites along a universal homeomorphism, which is the only remaining content of
  Stacks 04DZ, the remainder of which is
  `Stacks.Etale.etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj`; and
  `AlgebraicGeometry.IntegralHasFinitePresentationLimit`, which is Stacks 09YZ over a
  quasi-compact quasi-separated base and is what Stacks 05YU still needs.  Stacks 05YX, the
  companion of Stacks 04DZ for affine étale objects, is proved from exactly those two in
  `Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ`.
* The general lemmas are stated for an arbitrary `MorphismOfTopoi` because that is the level at
  which they are true; they are placed here, next to their only consumer, rather than in
  `StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi`.  There is deliberately no new
  definition: the packaged equivalence of the two
  functors is `CategoryTheory.Adjunction.toEquivalence`, whose `functor` and `inverse` are
  already identified with `f⁻¹` and `f_*` by Mathlib's generated
  `CategoryTheory.Adjunction.toEquivalence_functor` and `..._inverse`.

## References

* [Stacks Project, Tag 09AB](https://stacks.math.columbia.edu/tag/09AB)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 098T](https://stacks.math.columbia.edu/tag/098T)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 05YX](https://stacks.math.columbia.edu/tag/05YX)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace MorphismOfTopoi

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]

/-- If the inverse image of a morphism of topoi is an equivalence, so is its direct image. -/
public theorem isEquivalence_pushforward (g : MorphismOfTopoi E F)
    [g.inverseImage.IsEquivalence] : g.pushforward.IsEquivalence :=
  g.adj.isEquivalence_right_of_isEquivalence_left

end MorphismOfTopoi

namespace AlgebraicGeometry.ProEtale

universe u

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- The inverse-image half of Stacks 09AB follows from its direct-image half, with no
geometric input: the two functors are an adjoint pair. -/
public theorem smallProetaleInverseImage_isEquivalence_of_pushforward
    [(smallProetaleMorphism B T S f).pushforward.IsEquivalence] :
    (smallProetaleMorphism B T S f).inverseImage.IsEquivalence :=
  (smallProetaleMorphism B T S f).isEquivalence_inverseImage

/-- The direct-image half of Stacks 09AB follows from its inverse-image half, with no
geometric input. -/
public theorem smallProetalePushforward_isEquivalence_of_inverseImage
    [(smallProetaleMorphism B T S f).inverseImage.IsEquivalence] :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence :=
  (smallProetaleMorphism B T S f).isEquivalence_pushforward

/-- Site-level criterion for the direct-image half of Stacks 09AB: if base change along `f`
exhibits the small pro-étale site of `S` as a dense subsite of the small pro-étale site of `T`,
then the direct image of the induced morphism of topoi is an equivalence.

The direct image is restriction of sheaves along base change, so this is the comparison lemma
in the form `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`. -/
public theorem smallProetalePushforward_isEquivalence_of_isDenseSubsite
    (h : (smallProetaleBaseChange B T S f).IsDenseSubsite
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)) :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence := by
  have := h
  show ((smallProetaleBaseChange B T S f).sheafPushforwardContinuous
    (Type (u + 1)) (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)).IsEquivalence
  infer_instance

/-- Site-level criterion for the inverse-image half of Stacks 09AB, obtained from the
direct-image criterion by adjunction. -/
public theorem smallProetaleInverseImage_isEquivalence_of_isDenseSubsite
    (h : (smallProetaleBaseChange B T S f).IsDenseSubsite
      (SmallProetale.topology B S.obj S.property)
      (SmallProetale.topology B T.obj T.property)) :
    (smallProetaleMorphism B T S f).inverseImage.IsEquivalence :=
  have := smallProetalePushforward_isEquivalence_of_isDenseSubsite B T S f h
  (smallProetaleMorphism B T S f).isEquivalence_inverseImage

end AlgebraicGeometry.ProEtale

end
