module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModificationRepresentable

/-!
# Glueing étale sheaves and étale spaces along a proper modification

Let `S` be a scheme, let `f : Y ⟶ X` be a proper morphism of algebraic spaces over `S`, let
`i : Z ⟶ X` be a closed immersion and let `E = Z ×_X Y`:

```
E --j--> Y
|g       |f
v        v
Z --i--> X
```

If `f` is an isomorphism over the open complement `X ∖ Z`, then restriction
`F ↦ (f⁻¹F, i⁻¹F)` identifies the étale sheaves on `X` with the categorical pullback of the étale
sheaves on `Y` and `Z` over those on `E` (Stacks 0GFY), and base change `V ↦ (V ×_X Y, V ×_X Z)`
identifies the spaces-étale site of `X` with the categorical pullback of the spaces-étale sites
of `Y` and `Z` over that of `E` (Stacks 0GG1).

Both are the statements of
`AlgebraicGeometry.Space.isEquivalence_spacesModificationRestriction` and
`AlgebraicGeometry.Space.isEquivalence_spacesEtaleModificationRestriction_of_isEquivalence`, with
their base-change input supplied by proper base change for sheaves of sets on algebraic spaces
(Stacks 0DG0), `AlgebraicGeometry.Space.spacesToposBaseChangeSquare_isIso_of_isProper`.

The topos of sheaves on the small étale site `X_étale` is that of the spaces-étale site
(Stacks 03G1); the statements are made on the spaces-étale topoi, where the restriction and
glueing functors live.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_spacesModificationRestriction_of_isProper`:
  Stacks 0GFY.
* `AlgebraicGeometry.Space.isEquivalence_spacesEtaleModificationRestriction_of_isProper`:
  Stacks 0GG1.

## References

* [Stacks Project, Tag 0GFY](https://stacks.math.columbia.edu/tag/0GFY)
* [Stacks Project, Tag 0GG1](https://stacks.math.columbia.edu/tag/0GG1)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z E : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) (j : E ⟶ Y) (g : E ⟶ Z)

/-- **[Stacks, Tag 0GFY].** Let `S` be a scheme, let `f : Y ⟶ X` be a proper morphism of
algebraic spaces over `S`, let `i : Z ⟶ X` be a closed immersion, and let `E = Z ×_X Y` with
projections `j : E ⟶ Y` and `g : E ⟶ Z`. Suppose `f` is an isomorphism over the open complement
`u : X ∖ Z ⟶ X` of `Z`: the projection `fU : V ⟶ X ∖ Z` of a fibre product
`V = (X ∖ Z) ×_X Y` is an isomorphism. Then the functor
`Sh(X_étale) ⥤ Sh(Y_étale) ×_{Sh(E_étale)} Sh(Z_étale)`, `F ↦ (f⁻¹F, i⁻¹F)`, is an equivalence
of categories. -/
@[stacks 0GFY]
theorem isEquivalence_spacesModificationRestriction_of_isProper
    (hf : IsProper B S hS f.hom) (hi : IsClosedImmersion B S hS i.hom)
    (sq : IsPullback j g f i)
    {V : AlgebraicSpaces B S hS} (w' : V ⟶ Y)
    (fU : V ⟶ closedImmersionComplement B S hS i hi) [IsIso fU]
    (sqU : IsPullback w' fU f (closedImmersionComplementHom B S hS i hi)) :
    (spacesModificationRestriction B S hS f i j g sq.w).IsEquivalence :=
  isEquivalence_spacesModificationRestriction B S hS f i j g sq
    (spacesToposBaseChangeSquare_isIso_of_isProper B S hS f hf i j g sq) hi w' fU sqU

/-- **[Stacks, Tag 0GG1].** Let `S` be a scheme, let `f : Y ⟶ X` be a proper morphism of
algebraic spaces over `S`, let `i : Z ⟶ X` be a closed immersion, and let `E = Z ×_X Y` with
projections `j : E ⟶ Y` and `g : E ⟶ Z`. Suppose `f` is an isomorphism over the open complement
`u : X ∖ Z ⟶ X` of `Z`: the projection `fU : V ⟶ X ∖ Z` of a fibre product
`V = (X ∖ Z) ×_X Y` is an isomorphism. Then the functor
`X_{spaces,étale} ⥤ Y_{spaces,étale} ×_{E_{spaces,étale}} Z_{spaces,étale}`,
`V ↦ (V ×_X Y, V ×_X Z)`, is an equivalence of categories. -/
@[stacks 0GG1]
theorem isEquivalence_spacesEtaleModificationRestriction_of_isProper
    (hf : IsProper B S hS f.hom) (hi : IsClosedImmersion B S hS i.hom)
    (sq : IsPullback j g f i)
    {V : AlgebraicSpaces B S hS} (w' : V ⟶ Y)
    (fU : V ⟶ closedImmersionComplement B S hS i hi) [IsIso fU]
    (sqU : IsPullback w' fU f (closedImmersionComplementHom B S hS i hi)) :
    (spacesEtaleModificationRestriction B S hS f i j g sq.w).IsEquivalence :=
  have := isEquivalence_spacesModificationRestriction_of_isProper B S hS f i j g hf hi sq w' fU sqU
  isEquivalence_spacesEtaleModificationRestriction_of_isEquivalence B S hS f i j g sq.w

end AlgebraicGeometry.Space
