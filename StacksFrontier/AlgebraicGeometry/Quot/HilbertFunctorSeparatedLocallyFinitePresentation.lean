module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafModelLimitPreserving

/-!
# The Hilbert functor is separated and locally of finite presentation over the base

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
separated and of finite presentation. Stacks 0DM7 asserts that the morphism
`Hilb_{X/B} ⟶ B` is separated and locally of finite presentation.

The Hilbert presheaf of Stacks 0CZY takes values one universe up, so the statement is about its
canonical model in the universe of the site,
`AlgebraicGeometry.Space.HilbertPresheafModel.canonical`. Separatedness is the closedness of the
diagonal of Stacks 0DM6, through
`AlgebraicGeometry.Space.HilbertPresheafModel.isSeparated_toBase`; local finite presentation is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_toBase_canonical`, the limit argument of
Stacks 0D01 carried out for directed inverse systems of affine schemes of arbitrary size.

## Main results

* `HilbertPresheafModel.isSeparated_and_isLocallyOfFinitePresentation_toBase`: for `f`
  separated and of finite presentation, `Hilb_{X/B} ⟶ B` is separated and locally of finite
  presentation.

## References

* [Stacks Project, Tag 0DM7](https://stacks.math.columbia.edu/tag/0DM7)
* [Stacks Project, Tag 0DM6](https://stacks.math.columbia.edu/tag/0DM6)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` which is separated and of finite
presentation, the morphism `Hilb_{X/Y} ⟶ Y` from the Hilbert functor of Stacks 0CZY to the base
— read on the canonical model of the Hilbert presheaf in the universe of the site — is separated
and locally of finite presentation. -/
@[stacks 0DM7]
theorem HilbertPresheafModel.isSeparated_and_isLocallyOfFinitePresentation_toBase
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hsep : IsSeparated B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) :
    IsSeparated B S hS (HilbertPresheafModel.canonical f).toBase ∧
      IsLocallyOfFinitePresentation B S hS (HilbertPresheafModel.canonical f).toBase :=
  ⟨(HilbertPresheafModel.canonical f).isSeparated_toBase hfp,
    isLocallyOfFinitePresentation_toBase_canonical hfp hsep⟩

end AlgebraicGeometry.Space

end
