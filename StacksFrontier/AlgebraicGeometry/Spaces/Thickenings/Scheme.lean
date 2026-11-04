module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Closed subspaces of a scheme, and the thin side of a thickening

A closed immersion of algebraic spaces over `S` is representable, so a presheaf admitting a
closed immersion to a representable presheaf is representable: a closed subspace of a scheme
is a scheme. Applied to the inclusion of a thickening `X ⊂ X'` this says that if the ambient
space `X'` is a scheme then so is the closed subspace `X`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion`: a presheaf admitting a
  closed immersion to a representable presheaf is representable.
* `AlgebraicGeometry.Space.isRepresentable_of_isClosedSubspace`: a closed subspace of a
  representable presheaf is representable.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickening`: in a thickening `X ⊂ X'` of
  algebraic spaces over `S`, if `X'` is (representable by) a scheme then so is `X`.

## Implementation notes

Surjectivity on points plays no part in any of this, so the first two results are stated for
a closed immersion and a closed subspace, with no thickening hypothesis, and the thickening
statement is their corollary. Nothing here is Stacks 05ZR, which runs the other way: 05ZR
says that if the closed subspace `X` of a thickening is a scheme then the ambient space `X'`
is a scheme. That direction is not proved here — see the implementation notes below — and no
declaration in this file carries `@[stacks 05ZR]` or `@[stacks 0BPW]`.

*Why the converse is absent.* Stacks 05ZR is proved either from Limits of Spaces, Lemma
07VU (an algebraic space whose reduction is a scheme is a scheme) or, for finite order
thickenings, by reducing to the case of an affine `X` and exhibiting `X'` as
`Spec Γ(X', 𝒪_{X'})`. The *first* route passes through Limits of Spaces, Proposition 07VT —
an algebraic space receiving a surjective universally closed morphism from an affine scheme is
affine. That proposition and Lemma 07VS are in this library, as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed` and
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite` in
`StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection`, but each carries
three granted hypotheses — the conclusions of Stacks 09YA (respectively 07VR) and of Stacks
07SQ, and its own finite-presentation special case — so neither is available here without
those.

The *second* route does not pass through 07VT at all, and its topological and étale-site
inputs are all present in this library: Tag 05ZP is
`AlgebraicGeometry.Space.existsUnique_isOpenSubspace_preimage_eq_of_isThickening`, Tag 05Z1 is
`AlgebraicGeometry.Space.morphismToAffineEquiv`, Tag 05W5 is
`AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`, and
Tag 05ZH is proved at a thickening of *arbitrary* order as
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` together with
`AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfMonoOfIsThickening`. What blocks that route
here is Tag 05ZQ: the library's form,
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_projection_of_isThickening`, obtains
affineness of the ambient étale object from Stacks 07VS, so it carries those same three
granted hypotheses. And even unblocked the route would not give the tag: its comparison
morphism `X' ⟶ Spec Γ(X', 𝒪_{X'})` is shown étale using that the ideal is a module over
`Γ(X, 𝒪_X)`, which needs a square-zero ideal, so the route is intrinsically of finite order.

The purely topological part of 05ZR's reduction *is* available here, through Tag 03BZ and
Tag 03KE, so what is missing is exactly the affine case — and that is where the source's own
general case lands as well, since 05ZR reduces to an affine `X` by Tag 03JH and Tag 05ZP.
Specialising the thin side to an affine scheme is therefore not a weaker problem than the tag.

*Generality.* The two general statements are about an arbitrary presheaf on the big fppf site
of `S`, not only an algebraic space: the proof needs only that the closed immersion is
relatively representable, which is part of the definition of a closed immersion. The
algebraicity hypotheses enter only through the thickening corollary, whose statement mentions
the category of algebraic spaces.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf on the big fppf site of `S` admitting a closed immersion to a representable
presheaf is representable: a closed immersion is relatively representable, so Tag 03KC
applies. -/
theorem isRepresentable_of_isClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : IsClosedImmersion B S hS f) (hG : G.IsRepresentable) :
    F.IsRepresentable :=
  have := hG
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable f hf.rep

/-- A closed subspace of a representable presheaf on the big fppf site of `S` is
representable: a closed subspace of a scheme is a scheme. -/
theorem isRepresentable_of_isClosedSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor F} (hG : IsClosedSubspace B S hS G) (hF : F.IsRepresentable) :
    G.toFunctor.IsRepresentable :=
  isRepresentable_of_isClosedImmersion B S hS G.ι hG.2 hF

/-- In a thickening `X ⊂ X'` of algebraic spaces over `S`, if the ambient space `X'` is
(representable by) a scheme then so is the closed subspace `X`.

This is the elementary direction: it uses only that the inclusion of a thickening is a closed
immersion, hence relatively representable, and not that it is surjective on points. The other
direction is Stacks 05ZR, which is not proved here. -/
theorem isRepresentable_of_isThickening {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) (hX : X.1.IsRepresentable) :
    G.toFunctor.IsRepresentable :=
  isRepresentable_of_isClosedSubspace B S hS hG.1 hX

end AlgebraicGeometry.Space

end
