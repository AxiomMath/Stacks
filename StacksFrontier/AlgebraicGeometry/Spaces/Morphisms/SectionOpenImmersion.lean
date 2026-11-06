module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Sections of unramified morphisms of algebraic spaces

A section `s : V ⟶ P` of a morphism `p : P ⟶ V` of algebraic spaces over `S` is an open
immersion as soon as `p` is unramified, and in particular as soon as `p` is étale. This
complements the family of Stacks 03KP, whose entries record that a section is a monomorphism,
representable, locally of finite type, locally quasi-finite and separated with no hypothesis on
`p`, an immersion when `p` is locally separated and a closed immersion when `p` is separated.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_of_isUnramified_of_section`: a section of an
  unramified morphism of algebraic spaces over `S` is an open immersion.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_section`: a section of an étale
  morphism of algebraic spaces over `S` is an open immersion.

## Implementation notes

The proof is the one the 03KP family uses. A section of `p` is, as an object of the arrow
category, the comparison `V ×[P] P ⟶ V ×[V] P` of two fibre products, which is
`AlgebraicGeometry.Space.arrowIsoMapDescSection`; that comparison is a base change of the
relative diagonal of `p` by the magic diagram of Stacks 03KN; the relative diagonal of an
unramified morphism is an open immersion by part (1) of Stacks 05W1; and being an open immersion
is stable under base change, being a relatively representable property.

Nothing is carried as an extra hypothesis: the algebraic-space hypotheses on `P` and on `V` are
exactly the ones part (1) of Stacks 05W1 asks for, and no hypothesis at all is needed on the
section.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {P V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SectionOpenImmersion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_SectionOpenImmersion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A section of an unramified morphism of algebraic spaces over `S` is an open immersion: it is
the comparison of two fibre products, hence a base change of the relative diagonal of the
morphism, which is an open immersion. -/
theorem isOpenImmersion_of_isUnramified_of_section
    (hP : IsAlgebraicSpace B S hS P) (hV : IsAlgebraicSpace B S hS V) (p : P ⟶ V)
    (hp : IsUnramified B S hS p) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsOpenImmersion B S hS s :=
  (MorphismProperty.arrow_mk_iso_iff _ (arrowIsoMapDescSection B S hS p s hs)).1
    (presheaf_of_isPullback B S hS (isPullback_mapDesc B S hS s (𝟙 P) p)
      (isOpenImmersion_diagonal_of_isUnramified B S hS hP hV p hp))

/-- **Unramifiedness descends from the second projection of the self-fibre-product.** If
`f : P ⟶ V` is a morphism of algebraic spaces over `S` which is locally of finite type, and the
second projection `P ×_V P ⟶ P` is unramified, then `f` itself is unramified.

The relative diagonal of `f` is a section of that projection, so it is an open immersion by
`AlgebraicGeometry.Space.isOpenImmersion_of_isUnramified_of_section`, and part (2) of
**Stacks 05W1** concludes. This is the unramified twin of
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd`; the
hypothesis is available in particular when `f` is a base change of an unramified morphism along
itself. -/
theorem isUnramified_of_isUnramified_pullbackSnd
    (hP : IsAlgebraicSpace B S hS P) (hV : IsAlgebraicSpace B S hS V) (f : P ⟶ V)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hsnd : IsUnramified B S hS (pullback.snd f f)) :
    IsUnramified B S hS f :=
  isUnramified_of_isOpenImmersion_pullbackDiagonal B S hS hP hV f hft
    (isOpenImmersion_of_isUnramified_of_section B S hS
      (isAlgebraicSpace_pullback B S hS f f hP hP hV) hP (pullback.snd f f) hsnd
      (pullback.diagonal f) (pullback.diagonal_snd f))

/-- A section of an étale morphism of algebraic spaces over `S` is an open immersion, an étale
morphism being unramified. -/
@[ega "IV 17.9.3" "more general"]
theorem isOpenImmersion_of_isEtale_of_section
    (hP : IsAlgebraicSpace B S hS P) (hV : IsAlgebraicSpace B S hS V) (p : P ⟶ V)
    (hp : IsEtale B S hS p) (s : V ⟶ P) (hs : s ≫ p = 𝟙 V) :
    IsOpenImmersion B S hS s :=
  isOpenImmersion_of_isUnramified_of_section B S hS hP hV p
    (isUnramified_of_isEtale B S hS hp) s hs

end AlgebraicGeometry.Space

end
