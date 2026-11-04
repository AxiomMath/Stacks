module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Base change of an algebraic space along an algebra over its ring of global functions

Let `X` be an algebraic space all of whose quasi-coherent modules have vanishing first
cohomology, that is the data of Stacks 07UY, and write `A = Γ(X, 𝒪_X)`.  Clause (2) of
Stacks 07V0 asserts that for every `A`-algebra `A'` the base change
`X' = X ×_{Spec A} Spec A'` is affine over `X` and satisfies `Γ(X', 𝒪_{X'}) = A'`.

The canonical morphism `X ⟶ Spec A` is built here from the universal property of Stacks 05Z1:
morphisms of algebraic spaces from `X` to an affine object of the site are ring homomorphisms
out of its global functions, so an affine object whose global functions are identified with `A`
receives a morphism from `X` inducing that identification.  The affineness assertion then
follows from stability of affine morphisms under base change.

## Main definitions

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctions` is the canonical
  morphism `X ⟶ Spec A`, for an affine object of the site presenting `Spec A`.

## Main results

* `…CohomologyVanishingSituation.pullbackToGlobalFunctions_toSpecGlobalFunctions`: the canonical
  morphism induces the given identification on global functions.  This is what makes it
  canonical rather than an arbitrary morphism.
* `…CohomologyVanishingSituation.isAffineHom_of_isPullback_toSpecGlobalFunctions` and
  `…isAffineHom_snd_fiberProduct_toSpecGlobalFunctions`: **the affineness assertion of clause (2)
  of Stacks 07V0**, for an arbitrary Cartesian square and for the canonical fibre product
  respectively.

## Implementation notes

*How `Spec A` enters.*  Every algebraic space of this development is a presheaf on a fixed big
fppf site, so a scheme can only be used as a target if it is an object of that site; `Spec A` is
therefore presented by an object `V` of the site whose underlying scheme is affine, together
with a ring isomorphism `Γ(V, 𝒪_V) ≅ Γ(X, 𝒪_X)`.  This is not a restriction of the source's
statement but the form the statement takes over a fixed site, and it is how
Stacks 05Z1, `AlgebraicGeometry.Space.morphismToAffineEquiv`, is stated in the library.

Note that the ring of global functions `AlgebraicGeometry.Space.globalFunctions` is a limit over
the étale charts, a category whose objects lie one universe above the schemes, so `A` is a
`Type (u + 1)` as it stands and `Spec A` is not literally a scheme of the site; the hypothesis
above asks instead for a scheme of the site whose global functions are isomorphic to `A`, which
exists because the small étale site is essentially small at the universe of the schemes
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`).

*Why the base is terminal.*  The library's Stacks 05Z1 requires it, in order to read a morphism of
the underlying schemes of two objects of the site as a morphism over the base
(`AlgebraicGeometry.Space.overMapOfSchemeHom`).  Stacks 07V0 is a statement about `X` and its
own global functions, in which the base plays no part, and over the terminal scheme that is
literally what is stated.

*What is not proved.*  The computation `Γ(X', 𝒪_{X'}) = A'` of clause (2) is not treated.  The
source obtains it from the identification of `(X' → X)_*𝒪_{X'}` with `A' ⊗_A 𝒪_X`, which is an
assertion of Stacks 07U8 that the library's form of that tag does not cover —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` carries only
the quasi-coherence assertion — followed by Stacks 07UZ, which *is* available, as
`Stacks.Cohomology.SiteModules.isIso_sectionTensorSheafUnit_of_free`.  So the one missing step
is a named assertion of a formalized tag, not a missing tag.

*The base change itself* is Stacks 03WI, `AlgebraicGeometry.Space.IsAffineHom.of_isPullback`,
the lemma the source cites, applied to the Cartesian square read in presheaves by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`.  Affineness of the morphism being based
changed is `AlgebraicGeometry.Space.isAffineHom_yoneda_map`, the source's second citation: a
morphism of affine objects of the site is an affine morphism of algebraic spaces.

*Clause (1) of Stacks 07V0 is proved separately*, in
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffine`, whose implementation notes
record the four inputs it carries.

## References

* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m}) (hterminal : IsTerminal T.base)
    (V : BigFppfOver T.site T.base T.containsBase)
    [IsAffine ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V, ⊤) ≃+*
      _root_.AlgebraicGeometry.Space.globalFunctions T.site T.base T.containsBase T.space.1)

/-- **The canonical morphism `X ⟶ Spec A`** of Stacks 07UY, where `A = Γ(X, 𝒪_X)` and `Spec A`
is presented by an affine object `V` of the site through a ring isomorphism
`Γ(V, 𝒪_V) ≅ A`.

It is the morphism of algebraic spaces whose action on global functions is that isomorphism,
supplied by the universal property of Stacks 05Z1. -/
def toSpecGlobalFunctions : T.space ⟶ _root_.AlgebraicGeometry.schemeSpace V :=
  (morphismToAffineEquiv T.site T.base T.containsBase T.space V hterminal).1.symm e.toRingHom

/-- The canonical morphism to `Spec A` pulls global functions back along the given
isomorphism, which is what pins it down among all morphisms `X ⟶ Spec A`. -/
theorem pullbackToGlobalFunctions_toSpecGlobalFunctions :
    pullbackToGlobalFunctions T.site T.base T.containsBase T.space V
        (toSpecGlobalFunctions T hterminal V e) =
      e.toRingHom :=
  (morphismToAffineEquiv T.site T.base T.containsBase T.space V hterminal).1.apply_symm_apply _

/-- **The affineness assertion of clause (2) of Stacks 07V0.** Let `X` be as in Stacks 07UY, let
`A = Γ(X, 𝒪_X)`, and let `A'` be an `A`-algebra, presented by a morphism `q : W ⟶ V` of affine
objects of the site over the presentation of `Spec A`.  Then the projection
`X' = X ×_{Spec A} Spec A' ⟶ X` is affine.

A morphism of affine objects of the site is an affine morphism of algebraic spaces, and affine
morphisms are stable under base change, which is Stacks 03WI. -/
@[stacks 07V0 "clause (2), the affineness assertion only: the projection
X ×_{Spec A} Spec A' → X is affine. The computation Γ(X', 𝒪_{X'}) = A' of the same clause is
NOT proved -- it needs the pushforward-computation assertion of Stacks 07U8, which the library's
form of that tag does not carry. See this file's implementation notes, and for clause (1) see
StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingAffine.lean"]
theorem isAffineHom_of_isPullback_toSpecGlobalFunctions
    {W : BigFppfOver T.site T.base T.containsBase}
    [IsAffine ((BigFppfOver.toScheme T.site T.base T.containsBase).obj W)]
    (q : W ⟶ V) {X' : AlgebraicSpaces T.site T.base T.containsBase}
    {pr : X' ⟶ T.space} {pr' : X' ⟶ _root_.AlgebraicGeometry.schemeSpace W}
    (sq : IsPullback pr' pr (_root_.AlgebraicGeometry.schemeSpaceMap q)
      (toSpecGlobalFunctions T hterminal V e)) :
    IsAffineHom T.site T.base T.containsBase pr.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
    (isAffineHom_yoneda_map T.site T.base T.containsBase q)

/-- The affineness assertion of clause (2) of Stacks 07V0 for the canonical fibre product of
Stacks 02X2: the second projection of `Spec A' ×_{Spec A} X` is affine. -/
theorem isAffineHom_snd_fiberProduct_toSpecGlobalFunctions
    {W : BigFppfOver T.site T.base T.containsBase}
    [IsAffine ((BigFppfOver.toScheme T.site T.base T.containsBase).obj W)]
    (q : W ⟶ V) :
    IsAffineHom T.site T.base T.containsBase
      (pullback.snd (_root_.AlgebraicGeometry.schemeSpaceMap q).hom
        (toSpecGlobalFunctions T hterminal V e).hom) :=
  isAffineHom_of_isPullback_toSpecGlobalFunctions T hterminal V e q
    (AlgebraicSpaces.isPullback_fiberProduct T.site T.base T.containsBase _ _)

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
