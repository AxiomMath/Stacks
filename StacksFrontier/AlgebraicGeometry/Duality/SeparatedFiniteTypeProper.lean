module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Morphisms of `FTS S` are separated and of finite type, and properness is universal closedness

In the setting of [Stacks, Tag 0F42] the base `S` is Noetherian and `AlgebraicGeometry.FTS S`
is the category of schemes separated and of finite type over it. The structure morphisms of its
objects are separated and of finite type by definition; this file records that the *morphisms*
of `FTS S` are too, and draws the consequences.

The triangle `f.left ≫ Y.hom = X.hom` of a morphism `f : X ⟶ Y` of `FTS S` lets each condition
be cancelled off the structure morphism of the source: separatedness by
`AlgebraicGeometry.IsSeparated.of_comp` and finite type by
`AlgebraicGeometry.locallyOfFiniteType_of_comp`, neither of which asks anything of `Y.hom`.
Quasi-compactness of `f.left` comes instead from the source being a Noetherian scheme. Since
Mathlib's `AlgebraicGeometry.IsProper` is separatedness, universal closedness and finite type,
what is left of properness for a morphism of `FTS S` is universal closedness alone.

## Main results

* `AlgebraicGeometry.FTS.isNoetherian`: an object of `FTS S` is a Noetherian scheme when `S`
  is one. This is what supplies the Noetherian hypotheses that the duality results of
  Chapter 48, Section 3 ask of the source and target.
* `AlgebraicGeometry.FTS.isSeparated_left` and
  `AlgebraicGeometry.FTS.locallyOfFiniteType_left`: a morphism of `FTS S` is separated and
  locally of finite type, with no hypothesis on `S`.
* `AlgebraicGeometry.FTS.isProper_left_of_universallyClosed`: a morphism of `FTS S` is proper
  as soon as it is universally closed.

## Implementation notes

All four are instances, stated for the underlying morphism of schemes `f.left` of a morphism
`f : X ⟶ Y` of `FTS S`, which is the form in which typeclass synthesis meets them and the form
in which the duality lemmas of this directory take their morphisms -- see
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts`, which writes `[IsClosedImmersion i.left]`.

`AlgebraicGeometry.FTS.isNoetherian` makes quasi-compactness of a morphism out of an object of
`FTS S` automatic, through Mathlib's
`AlgebraicGeometry.quasiCompact_of_noetherianSpace_source` and
`AlgebraicGeometry.IsNoetherian.noetherianSpace`, so no `QuasiCompact f.left` instance is
declared here. It is also why `isProper_left_of_universallyClosed` needs no Noetherian
hypothesis: `IsProper` does not include quasi-compactness, universal closedness already
implying it.

The commuting triangle is `CategoryTheory.MorphismProperty.Over.w`: the objects of `FTS S` are
`CategoryTheory.MorphismProperty.Over` for `AlgebraicGeometry.isSeparatedFiniteType` with `⊤`
on the morphisms, so a morphism of `FTS S` is in particular a morphism of `Over S`.

## References

* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FTS

variable {S : Scheme.{u}}

/-- An object of `FTS S` is a Noetherian scheme as soon as the base `S` is one: it is locally
Noetherian by `AlgebraicGeometry.FTS.isLocallyNoetherian` and quasi-compact by
`AlgebraicGeometry.FTS.compactSpace`. -/
instance isNoetherian [IsNoetherian S] (X : FTS S) : IsNoetherian X.left where

/-- A morphism of `FTS S` is separated. Separatedness cancels off a composition on the right
with no hypothesis on the second factor, and `f.left ≫ Y.hom` is the structure morphism of the
source, which is separated because its object lies in `FTS S`. -/
instance isSeparated_left {X Y : FTS S} (f : X ⟶ Y) : IsSeparated f.left := by
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [MorphismProperty.Over.w f]
    infer_instance
  exact IsSeparated.of_comp f.left Y.hom

/-- A morphism of `FTS S` is locally of finite type. As for separatedness, the condition cancels
off `f.left ≫ Y.hom = X.hom` with no hypothesis on `Y.hom`. -/
instance locallyOfFiniteType_left {X Y : FTS S} (f : X ⟶ Y) : LocallyOfFiniteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [MorphismProperty.Over.w f]
    infer_instance
  exact locallyOfFiniteType_of_comp f.left Y.hom

/-- A morphism of `FTS S` is proper as soon as it is universally closed: properness is
separatedness, universal closedness and finite type, and the first and third hold for every
morphism of `FTS S`. -/
instance isProper_left_of_universallyClosed {X Y : FTS S} (f : X ⟶ Y)
    [UniversallyClosed f.left] : IsProper f.left where

end FTS

end AlgebraicGeometry

end
