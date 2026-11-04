module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of an affine morphism

An affine morphism of schemes stays affine after base change along an arbitrary morphism: in a
cartesian square of schemes, the morphism opposite an affine morphism is again affine.

## Main results

* `AlgebraicGeometry.IsAffineHom.of_isPullback`: the morphism opposite an affine morphism in a
  cartesian square of schemes is affine.
* `AlgebraicGeometry.IsAffineHom.pullback_snd`: the second projection of a fibre product along
  an affine morphism is affine.

## References

* [Stacks Project, Tag 01SD](https://stacks.math.columbia.edu/tag/01SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change of an affine morphism is affine: if `f : X ⟶ S` is affine and
`g' ≫ f = f' ≫ g` is a cartesian square, then the base change `f' : X' ⟶ S'` of `f` along
`g : S' ⟶ S` is affine. -/
@[stacks 01SD]
lemma IsAffineHom.of_isPullback {X S X' S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g) [IsAffineHom f] :
    IsAffineHom f' :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) sq ‹IsAffineHom f›

/-- For an affine morphism `f : X ⟶ S` and any `g : S' ⟶ S`, the projection `X ×_S S' ⟶ S'` is
affine. -/
@[ega "II 1.5.5"]
lemma IsAffineHom.pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom f] :
    IsAffineHom (pullback.snd f g) :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback f g)

end AlgebraicGeometry
