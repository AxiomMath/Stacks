module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal

/-!
# Base change of finite locally free morphisms of algebraic spaces

A representable morphism of algebraic spaces over a scheme `S` is finite locally free when each
of its represented base changes is a finite locally free morphism of schemes, which is condition
(1) of Stacks 03ZW.  Such a morphism remains finite locally free after an arbitrary base change,
and so does its rank.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_isStableUnderBaseChange` and
  `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_of_isPullback`: **Stacks 03ZY**, as a
  base-change stable class of morphisms and at an arbitrary Cartesian square of presheaves;
  `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_pullback_snd` specialises the latter to
  the chosen fibre product.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_isStableUnderBaseChange`,
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_of_isPullback` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_pullback_snd`: the same three
  statements for a fixed rank.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_inverseImage_isStableUnderBaseChange` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_inverseImage_isStableUnderBaseChange`:
  finite local freeness of a morphism of the big fppf site of `S`, with or without a fixed rank,
  is stable under base change in that site.

## Implementation notes

Finite local freeness of a representable morphism of algebraic spaces is
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of finite local freeness of morphisms of schemes, as in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal`.  A property of that shape
asks of a morphism that every one of its represented base changes have the scheme-level
property, and the represented base changes of a base change of `f` are among those of `f`, the
two Cartesian squares pasting to exhibit each of them as one of `f`.  Base-change stability is
therefore `CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, which needs
nothing of finite local freeness.

What finite local freeness contributes is the scheme-level content: Tag 02KD, and its rank
refinement Tag 02KA, make the inverse image along `AlgebraicGeometry.BigFppfOver.toScheme`
stable under base change in the big fppf site of `S`, which is the shape in which a represented
base change of a morphism of the site is itself base changed.

Base change is stated at a Cartesian square of presheaves rather than at the chosen fibre
product, as elsewhere in this directory, so that it applies to any construction of the base
change; no algebraicity hypothesis on the four presheaves is used.

The definition of Stacks 03ZV, `AlgebraicGeometry.Space.IsFiniteLocallyFree` — affineness of `f`
together with finite local freeness of `f_*𝒪_X` on the small étale ringed site of the target —
is not treated here.  Its comparison with condition (1) of Stacks 03ZW is Stacks 03ZU, which is
proved, as `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`; what is still open is
only its rank form, where
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison` continues to
carry the rank chart comparison as a hypothesis.  Base change for the direct image would
in any case need the comparison of `f_*𝒪_X` with the direct image along the base change, which
is available on the small étale sites only for an étale base change.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KD](https://stacks.math.columbia.edu/tag/02KD)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 03ZY](https://stacks.math.columbia.edu/tag/03ZY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change in the big fppf site -/

/-- Finite local freeness of a morphism of the big fppf site of `S` is stable under base change
in that site.  This is Tag 02KD, transported along a functor to schemes which preserves fibre
products. -/
instance isFiniteLocallyFree_inverseImage_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  inverseImage_isStableUnderBaseChange B S hS inferInstance

/-- Being finite locally free of rank `r` is stable under base change in the big fppf site of
`S`.  This is Tag 02KA, transported along a functor to schemes which preserves fibre
products. -/
theorem isFiniteLocallyFreeOfRank_inverseImage_isStableUnderBaseChange (r : ℕ) :
    (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  inverseImage_isStableUnderBaseChange B S hS inferInstance

/-! ### Base change of a morphism of algebraic spaces -/

/-- **Stacks 03ZY.** Being representable and finite locally free is a base-change stable class
of morphisms of presheaves on the big fppf site of `S`. -/
@[stacks 03ZY "stability under base change"]
instance isFiniteLocallyFree_presheaf_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- **Stacks 03ZY.** A base change of a representable finite locally free morphism of algebraic
spaces over `S` is representable and finite locally free: if `f'` sits in a Cartesian square
over `f`, then `f'` is finite locally free as soon as `f` is. -/
@[stacks 03ZY]
theorem isFiniteLocallyFree_presheaf_of_isPullback
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f' :=
  (isFiniteLocallyFree_presheaf_isStableUnderBaseChange B S hS).of_isPullback sq hf

/-- The second projection of the chosen fibre product of a representable finite locally free
morphism of algebraic spaces over `S` along an arbitrary morphism is finite locally free. -/
theorem isFiniteLocallyFree_presheaf_pullback_snd
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) :=
  isFiniteLocallyFree_presheaf_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-! ### The same for a fixed rank -/

/-- Being representable and finite locally free of rank `r` is a base-change stable class of
morphisms of presheaves on the big fppf site of `S`.

Stacks 03ZY states no rank; the rank is part of the definition of Stacks 03ZV, and the
scheme-level statement that it is unchanged by base change is Tag 02KA. -/
theorem isFiniteLocallyFreeOfRank_presheaf_isStableUnderBaseChange (r : ℕ) :
    (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- A base change of a representable morphism of algebraic spaces over `S` which is finite
locally free of rank `r` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_presheaf_of_isPullback (r : ℕ)
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f' :=
  (isFiniteLocallyFreeOfRank_presheaf_isStableUnderBaseChange B S hS r).of_isPullback sq hf

/-- The second projection of the chosen fibre product of a representable morphism of algebraic
spaces over `S` which is finite locally free of rank `r`, along an arbitrary morphism, is finite
locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_presheaf_pullback_snd (r : ℕ)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) :=
  isFiniteLocallyFreeOfRank_presheaf_of_isPullback B S hS r (IsPullback.of_hasPullback f g) hf

end AlgebraicGeometry.Space

end
