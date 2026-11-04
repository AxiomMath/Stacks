module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafModelSeparated

/-!
# The Hilbert functor is separated over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation. Then `Hilb_{X/Y} ⟶ Y` is separated: its diagonal is a closed immersion.

The Hilbert presheaf takes values in `Type (u + 1)`, so separatedness of `Hilb_{X/Y} ⟶ Y` as a
morphism of presheaves in the universe of the site is a statement about a model of the Hilbert
presheaf (`AlgebraicGeometry.Space.HilbertPresheafModel`). It is proved here for every model, in
particular for the canonical one, which exists for every morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.HilbertPresheafModel.isSeparated_toBase`: the morphism to the base of
  any model of the Hilbert functor of a morphism of finite presentation is separated.

## References

* [Stacks Project, Tag 0DM7](https://stacks.math.columbia.edu/tag/0DM7)
* [Stacks Project, Tag 0DM6](https://stacks.math.columbia.edu/tag/0DM6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Hilb_{X/Y} ⟶ Y` is separated.** For a morphism `f : X ⟶ Y` of algebraic spaces of finite
presentation, the morphism to the base of any model of the Hilbert functor of `f` is separated:
its diagonal is a closed immersion. -/
theorem HilbertPresheafModel.isSeparated_toBase {f : X ⟶ Y}
    (hf : IsFinitePresentation B S hS f.hom) (M : HilbertPresheafModel f) :
    IsSeparated B S hS M.toBase :=
  M.isSeparated_toBase_iff.2 <|
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) inf_le_left) _
      (diagonal_hilbertPresheafToBase f hf)

end AlgebraicGeometry.Space

end
