module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverUniversalAtlas

/-!
# The atlas candidate of `ℋ_d` is representable by algebraic spaces

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` goes from the category
represented by the scheme of structure constants over `S` into the category `ℋ_d` of degree-`d`
finite locally free covers. The presentation clause of **Stacks 026O** asks of it three
properties — representability by algebraic spaces, surjectivity and smoothness — and this file
proves the first.

Nothing about the 1-morphism itself is used. Its source is a slice of the big fppf site of `S`,
and the diagonal of `ℋ_d` is representable by algebraic spaces by
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_finiteCoverFibered`; **Stacks 045G** turns the
second of those into representability of *every* 1-morphism into `ℋ_d` out of a slice, through
the equivalence of its conditions (2) and (3),
`AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes`. So the
statement below holds for every scheme-valued point of `ℋ_d`, and the atlas candidate is one.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_finiteCoverPoint`: every 1-morphism
  into `ℋ_d` from a slice of the big fppf site of `S` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas`: the
  atlas candidate of `ℋ_d` is representable by algebraic spaces.

## Implementation notes

The general statement is proved first and the atlas candidate is an instance of it, because
representability here is a property of the *target* rather than of the 1-morphism: Stacks 045G
reads the diagonal of `ℋ_d` as a statement about all scheme-valued points at once. Stating it
only for the atlas candidate would hide that, and the general form is what the surjectivity and
smoothness clauses need too — both are relative properties of **Stacks 03YK**, which presuppose
a witness of representability for the 1-morphism they constrain.

No `@[stacks]` attribute is placed here. The site of the implication used is
`AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes`, where
conditions (2) and (3) of Stacks 045G are proved equivalent, and the presentation clause of
Stacks 026O for `ℋ_d` asks for two further properties of the atlas candidate which are not
proved below.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)

/-- **Every scheme-valued point of `ℋ_d` is representable by algebraic spaces.** This is
condition (3) of **Stacks 045G** for the category of degree-`d` finite locally free covers, which
holds because its isomorphism sheaves are algebraic spaces — condition (2), proved in
`AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_finiteCoverFibered`. -/
theorem isRepresentableFromSchemes_finiteCoverFibered :
    IsRepresentableFromSchemes B S hS (finiteCoverFibered B S hS d) :=
  (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
      (finiteCoverFibered B S hS d)).mp
    (isAlgebraicSpaceIsomPresheaf_finiteCoverFibered B S hS d)

/-- **A degree-`d` cover of an object of the site gives a 1-morphism into `ℋ_d` that is
representable by algebraic spaces.** -/
theorem isRepresentableByAlgebraicSpaces_finiteCoverPointHom {W U : BigFppfOver B S hS}
    (c : W ⟶ U)
    (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map c) d) :
    IsRepresentableByAlgebraicSpaces B S hS (finiteCoverPointHom c hc).hom :=
  isRepresentableFromSchemes_finiteCoverFibered B S hS d U (finiteCoverPointHom c hc).hom

/-- **The atlas candidate of `ℋ_d` is representable by algebraic spaces.** This is the first of
the three properties the presentation clause of **Stacks 026O** asks of
`AlgebraicGeometry.Stack.finiteCoverUniversalAtlas`; it follows from representability of the
diagonal of `ℋ_d` by **Stacks 045G**, and uses nothing about the 1-morphism beyond its source
being a slice of the big fppf site of `S`. -/
theorem isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas [NeZero d] :
    IsRepresentableByAlgebraicSpaces B S hS (finiteCoverUniversalAtlas B S hS d).hom :=
  isRepresentableFromSchemes_finiteCoverFibered B S hS d (structureConstantsOver B S hS d)
    (finiteCoverUniversalAtlas B S hS d).hom

end AlgebraicGeometry.Stack

end
