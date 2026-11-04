module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdAffine

/-!
# Affineness of the complement of the diagonals

The complement `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` of the diagonals in a nonempty finite
self-product of an object `U` of the spaces-étale site of an algebraic space `X` is affine as
soon as `U` is affine and `X` is separated.

This is steps (b) and (c) of the affineness chain of the proof of [Stacks, Tag 072B]. Step (a),
affineness of the self-product itself, is
`AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_selfProd_succ`; step (b), that
`W ↪ U^n` is a *closed* immersion, is
`AlgebraicGeometry.Space.SpacesEtale.isClosedImmersion_diagonalComplementι`, which needs no
hypothesis on `X`; step (c), that a closed subspace of an affine space is affine, is the
statement `AlgebraicGeometry.Space.IsAffineSpace.of_isClosedImmersion` proved here.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.IsAffineSpace.of_isClosedImmersion`: the source of a closed
  immersion with affine target is affine.
* `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_diagonalComplement`: the
  complement of the diagonals in a nonempty finite self-product of an affine object over a
  separated base is affine.

## What is and is not proved

Nothing here carries a Stacks attribute. Step (c) is not new mathematics in either tree: at the
level of schemes it is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`, and at the level of
algebraic spaces it is [Stacks, Tag 07U2]
(`AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion`: a closed immersion is affine)
followed by `AlgebraicGeometry.Space.IsAffineHom.isAffineSpace_source`. What was missing was
only the composite, which is the one-line proof below.

The empty self-product is excluded for the same reason as in step (a): `U^0` is a final object
of the site, with `X` itself as underlying algebraic space.

## References

* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The source of a closed immersion of algebraic spaces with affine target is affine.** A
closed immersion is an affine morphism by [Stacks, Tag 07U2], and the source of an affine
morphism with affine target is affine.

This is step (c) of the affineness chain of [Stacks, Tag 072B], "a closed subspace of an affine
space is affine". The corresponding statement for schemes is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`, which in addition
records the surjectivity on global sections. -/
theorem IsAffineSpace.of_isClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsClosedImmersion B S hS f) (hG : IsAffineSpace B S hS G) :
    IsAffineSpace B S hS F :=
  IsAffineHom.isAffineSpace_source (isAffineHom_of_isClosedImmersion B S hS f hf) hG

variable (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- **The complement of the diagonals in a nonempty finite self-product of an affine object
over a separated base is affine.** If `X` is a separated algebraic space over `S` in the
absolute sense of [Stacks, Tag 03BS], the algebraic space underlying `U` is affine and the
structure morphism of `U` is separated, then the algebraic space underlying the space `W` of
[Stacks, Tag 0726] inside the `(n + 1)`-fold self-product is affine.

The self-product is affine by
`AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_selfProd_succ` and `W` is a
closed subspace of it by
`AlgebraicGeometry.Space.SpacesEtale.isClosedImmersion_diagonalComplementι`, so
`AlgebraicGeometry.Space.IsAffineSpace.of_isClosedImmersion` applies. Separatedness of the
structure morphism of `U` is used only for the closed immersion, and separatedness of `X` only
for the self-product. -/
theorem isAffineSpace_underlying_diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hU : IsAffineSpace B S hS (underlying B S hS X U).obj)
    (hX : IsAbsolutelySeparated B S hS hZ X.obj) :
    IsAffineSpace B S hS
      (underlying B S hS X (diagonalComplement B S hS X U (n + 1) hsep)).obj :=
  IsAffineSpace.of_isClosedImmersion B S hS
    (isClosedImmersion_diagonalComplementι B S hS X U (n + 1) hsep)
    (isAffineSpace_underlying_selfProd_succ B S hS hZ X U hU hX n)

end SpacesEtale

end AlgebraicGeometry.Space

end
