module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct

/-!
# Étaleness of a morphism out of a representable presheaf is local on the source

Let `S` be a scheme contained in a big fppf site `B`. A morphism `g : U ⟶ Z` out of the
universe-lifted Yoneda presheaf of an object `U` of the big fppf site of `S` is *étale* when
every representable base change of it is étale on underlying schemes, which is
`AlgebraicGeometry.Space.etaleOnSite` relative to `CategoryTheory.uliftYoneda`. This file
records that the condition may be checked after restricting to an open cover of `U`: étaleness
of such a morphism is local on the source.

The library's locality statement for a value universe independent of the universe of the
schemes was previously available only on the *target*, where it is used to read étaleness of a
morphism of formal algebraic spaces at one scheme-valued point of the target at a time. The
statement below is the companion on the source, and is what a clopen decomposition of the
source feeds: a section of a coproduct of sheaves splits the source into open pieces, one for
each member, and the restriction of the morphism to each piece is étale.

## Main results

* `AlgebraicGeometry.Space.relative_etaleOnSite_of_openCover_source`: **étaleness of a
  morphism out of a universe-lifted representable presheaf is local on the source.**

## Implementation notes

This is `AlgebraicGeometry.relative_inverseImage_of_openCover_source`, the general locality
statement for a Zariski-local-at-source property of scheme morphisms and a fully faithful
fibre-product-preserving functor from the site into its presheaves, read at
`CategoryTheory.uliftYoneda` and at `AlgebraicGeometry.Etale`. Nothing about the geometry is
redone: the proof of the general statement covers the represented fibre product by the base
changes of the members of the cover, which is a Zariski covering of it, and descends the
property along that covering.

## References

* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étaleness of a morphism out of a universe-lifted representable presheaf is local on the
source.** Let `g : uliftYoneda.obj V ⟶ Z` be a morphism of presheaves on the big fppf site of
`S` with values in `Type (max w u)`, representable by objects of the site, and let `{W k ⟶ V}`
be a family of open immersions covering `V`. If every restriction of `g` to a member of the
family is étale, in the sense that each of its representable base changes is étale on
underlying schemes, then so is `g`.

This is `AlgebraicGeometry.relative_inverseImage_of_openCover_source` read at
`CategoryTheory.uliftYoneda` and at `AlgebraicGeometry.Etale`, which is Zariski local at the
source. -/
theorem relative_etaleOnSite_of_openCover_source
    {V : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {g : (uliftYoneda.{w}).obj V ⟶ Z}
    (hrep : (uliftYoneda.{w}).relativelyRepresentable g)
    {K : Type v} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ V)
    (hoi : ∀ k, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj V,
      ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (h : ∀ k, (etaleOnSite B S hS).relative (uliftYoneda.{w})
      ((uliftYoneda.{w}).map (p k) ≫ g)) :
    (etaleOnSite B S hS).relative (uliftYoneda.{w}) g :=
  relative_inverseImage_of_openCover_source
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale))
    hrep p hoi hcov h

end AlgebraicGeometry.Space

end
