module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper

/-!
# Properness of the relative diagonal of a morphism of algebraic spaces (Stacks 04Y0)

Stacks 04Y0 says that for a morphism `f` of algebraic spaces over a scheme `S` the following
are equivalent: `f` is separated; its relative diagonal is universally closed; its relative
diagonal is proper. This file contains the two implications which follow from Stacks 04XZ,
and the criterion through which the remaining implication is to be obtained.

## Main results

* `AlgebraicGeometry.Space.isProper_diagonal_of_isSeparated` and
  `AlgebraicGeometry.Space.universallyClosed_diagonal_of_isSeparated` are the implications
  (1) ⇒ (3) and (1) ⇒ (2) of Stacks 04Y0.
* `AlgebraicGeometry.Space.isClosedImmersion_of_mono_of_charts` is the algebraic-space form
  of Stacks 04XV (6) ⇒ (1): a monomorphism of algebraic spaces over `S` whose represented
  base changes are universally closed and locally of finite type is a closed immersion.
* `AlgebraicGeometry.Space.isSeparated_of_diagonal_charts` is its specialisation to the
  relative diagonal, which is the implication (2) ⇒ (1) of Stacks 04Y0 up to the two
  hypotheses discussed below.

## Implementation notes

`AlgebraicGeometry.Space.IsSeparated` is by definition the relative diagonal being a closed
immersion, so (1) ⇒ (3) is Stacks 04XZ applied to the relative diagonal, whose target is an
algebraic space by Stacks 02X2; and (3) ⇒ (2) is the third component of
`AlgebraicGeometry.Space.IsProper`.

No declaration here carries `@[stacks 04Y0]`: the implication (2) ⇒ (1) is not proved. It is
`AlgebraicGeometry.Space.isSeparated_of_diagonal_charts`, which needs two statements about
the relative diagonal that this library does not yet have:

* that it is locally of finite type as a representable morphism, which is part (2) of Stacks
  03HK and rests on Stacks 02X4 and the étale-local criterion of Stacks 02WZ; and
* that universal closedness in the sense of Stacks 03HI — closedness on the points of every
  base change by an algebraic space — gives `AlgebraicGeometry.UniversallyClosed` for every
  *represented* base change, which is Stacks 03XD. The point-set dictionary for a
  represented base change is available
  (`AlgebraicGeometry.Space.isClosed_image_pointsToScheme` and
  `AlgebraicGeometry.Space.pointsToScheme_pointsMap`); what is missing is that Mathlib's
  `AlgebraicGeometry.UniversallyClosed` quantifies over base changes by *all* schemes, while
  Stacks 03HI quantifies over algebraic spaces over `S`, hence over schemes inside the chosen
  big fppf site.

Supplying those two terms turns `AlgebraicGeometry.Space.isSeparated_of_diagonal_charts` into
(2) ⇒ (1) and completes Stacks 04Y0 with no further work.

The scheme input to `AlgebraicGeometry.Space.isClosedImmersion_of_mono_of_charts` is
Mathlib's `AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`, which carries the tag
Stacks 04XV itself: a monomorphism of schemes is separated, so a universally closed
monomorphism locally of finite type is proper, hence a closed immersion. Monomorphy transfers
down to the represented base changes because being a monomorphism is stable under base
change, `CategoryTheory.yoneda` is faithful and
`AlgebraicGeometry.BigFppfOver.toScheme` preserves fibre products.

## References

* [Stacks Project, Tag 04Y0](https://stacks.math.columbia.edu/tag/04Y0)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A monomorphism of algebraic spaces over `S` all of whose represented base changes are
universally closed and locally of finite type is a closed immersion.

This is the algebraic-space form of Stacks 04XV (6) ⇒ (1); the scheme statement is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`. -/
theorem isClosedImmersion_of_mono_of_charts (g : X ⟶ Y) (hmono : Mono g)
    (hLFT : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hUC : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    IsClosedImmersion B S hS g := by
  refine ⟨hLFT.1, ?_⟩
  intro A C c fst snd sq
  have : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map snd) := hLFT.2 c fst snd sq
  have : AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B S hS).map snd) := hUC.2 c fst snd sq
  have : Mono snd := yoneda.mono_of_mono_map
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms _) sq hmono)
  exact (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
    ((BigFppfOver.toScheme B S hS).map snd)).2 ⟨⟨⟩, inferInstance⟩

/-- **Stacks 04Y0, (2) ⇒ (1)**, up to its two inputs: a morphism of algebraic spaces over `S`
whose relative diagonal is universally closed and locally of finite type on every represented
base change is separated.

The two hypotheses are part (2) of Stacks 03HK and the conclusion of Stacks 03XD applied to
universal closedness of the diagonal; neither is available in this library yet, which is why
no declaration here carries `@[stacks 04Y0]`. -/
theorem isSeparated_of_diagonal_charts (f : X ⟶ Y)
    (hLFT : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f))
    (hUC : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f)) :
    IsSeparated B S hS f :=
  isClosedImmersion_of_mono_of_charts B S hS (pullback.diagonal f) inferInstance hLFT hUC

/-- **Stacks 04Y0, (1) ⇒ (3).** The relative diagonal of a separated morphism of algebraic
spaces over `S` is proper, by Stacks 04XZ: separatedness *is* the diagonal being a closed
immersion. -/
theorem isProper_diagonal_of_isSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsSeparated B S hS f) :
    IsProper B S hS (pullback.diagonal f) :=
  isProper_of_isClosedImmersion B S hS hX
    (isAlgebraicSpace_pullback B S hS f f hX hX hY) (pullback.diagonal f) hf

/-- **Stacks 04Y0, (1) ⇒ (2).** The relative diagonal of a separated morphism of algebraic
spaces over `S` is universally closed. -/
theorem universallyClosed_diagonal_of_isSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsSeparated B S hS f) :
    UniversallyClosed B S hS (pullback.diagonal f) :=
  (isProper_diagonal_of_isSeparated B S hS hX hY f hf).2.2

end AlgebraicGeometry.Space

end
