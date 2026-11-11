module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffine

/-!
# The pushout of algebraic spaces along a thickening, under its primed name

For a thickening `X ⟶ X'` and an affine morphism `X ⟶ Y` of schemes over `S`, a pushout square
of schemes is also a pushout square in the algebraic spaces over `S`. This is Stacks 07SY,
proved as `AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom`;
this file restates it under the primed name its users cite.

## Main results

* `AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom'`: the
  statement of Stacks 07SY, derived from the unprimed theorem.

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-- For a thickening `X ⟶ X'` and an affine morphism `X ⟶ Y` of schemes over `S`, a pushout
square of schemes is also a pushout square in the algebraic spaces over `S`; this is
`isPushout_algebraicSpaces_of_isThickening_of_isAffineHom` (Stacks 07SY), under the name its
users cite. -/
theorem isPushout_algebraicSpaces_of_isThickening_of_isAffineHom'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    IsPushout
      (ObjectProperty.homMk (yoneda.map i) :
        (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map f) :
        (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map a) :
        (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y', isAlgebraicSpace_yoneda B S hS Y'⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map b) :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y', isAlgebraicSpace_yoneda B S hS Y'⟩ : AlgebraicSpaces B S hS)) :=
  isPushout_algebraicSpaces_of_isThickening_of_isAffineHom B S hS i f a b hi hPushout

end AlgebraicGeometry.Space

end
