module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor

/-!
# The relative derived Hom functor of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `K`, `E` be objects
of `D(𝒪_X)`.  For an algebraic space `V` over `Y` write `X_V = X ×_Y V` for the base change and
`K_V`, `E_V` for the derived pullbacks of `K` and `E` along the projection `X_V ⟶ X`.  Stacks
0DLC, part (3), and Stacks 0DLD, part (c), study the functor

> `V ↦ Hom_{D(𝒪_{X_V})}(K_V, E_V)`,

whose restriction map along a morphism `V' ⟶ V` over `Y` is derived pullback along the induced
morphism `X_{V'} ⟶ X_V`, read through the composition comparison of Stacks 0D6D.  This file
constructs it, on the algebraic spaces over `Y` and on the test schemes over `Y`.

## Main definitions

* `AlgebraicGeometry.Space.overBaseChangeCone`: the projections `X_V ⟶ X`, as a cone from the
  base change functor `V ↦ X_V` to `X`.
* `AlgebraicGeometry.Space.relativeDerivedHomOver`: the functor `V ↦ Hom(K_V, E_V)` on the
  algebraic spaces `V` over `Y`.
* `AlgebraicGeometry.Space.relativeDerivedHom`: its restriction to the test schemes over `Y`,
  the shape the representability predicate
  `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver` consumes.

## Implementation notes

The functor is the generic relative Hom functor `CategoryTheory.PullbackData.relHomFunctor` of
the coherent pullback pseudofunctor datum
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, at the cone of projections out of the
base changes.  Its functoriality is therefore the unit law and the associativity coherence of
that datum, `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_isCoherent`, and nothing is
proved here by hand.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- The projections `X_V ⟶ X` out of the base changes of `f : X ⟶ Y` along the algebraic spaces
`V` over `Y`, as a cone from the base change functor `V ↦ X_V` to `X`. -/
def overBaseChangeCone (f : X ⟶ Y) :
    PullbackData.ConeTo (overBaseChangeFunctor f ⋙ Over.forget X) X where
  leg V := overProjection f V
  w g := overBaseChangeMap_comp_projection f g

/-- **The relative derived Hom functor on the algebraic spaces over `Y`.**  For a morphism
`f : X ⟶ Y` of algebraic spaces and objects `K`, `E` of `D(𝒪_X)`, the functor sending an
algebraic space `V` over `Y` to `Hom_{D(𝒪_{X_V})}(K_V, E_V)`, where `K_V` and `E_V` are the
derived pullbacks of `K` and `E` along the projection `X_V ⟶ X`, and a morphism `V' ⟶ V` over `Y`
to derived pullback along the induced morphism `X_{V'} ⟶ X_V`. -/
def relativeDerivedHomOver (f : X ⟶ Y) (K E : derivedModules B S hS X) :
    (Over Y)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleDerivedPullbackData B S hS).relHomFunctor
    (smallEtaleDerivedPullbackData_isCoherent B S hS) (overBaseChangeCone f) K E

/-- The value of the relative derived Hom functor at an algebraic space `V` over `Y` is the set
of morphisms `K_V ⟶ E_V` of `D(𝒪_{X_V})`. -/
theorem relativeDerivedHomOver_obj (f : X ⟶ Y) (K E : derivedModules B S hS X) (V : Over Y) :
    (relativeDerivedHomOver f K E).obj (Opposite.op V) =
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E) :=
  rfl

/-- **The relative derived Hom functor on the test schemes over `Y`**, `T ↦ Hom(K_T, E_T)`: the
restriction of `AlgebraicGeometry.Space.relativeDerivedHomOver` along the test schemes over
`Y`, regarded as algebraic spaces over `Y`. -/
def relativeDerivedHom (f : X ⟶ Y) (K E : derivedModules B S hS X) :
    (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  (schemesOverToOver Y).op ⋙ relativeDerivedHomOver f K E

/-- The value of the relative derived Hom functor at a test scheme `T` over `Y` is the set of
morphisms `K_T ⟶ E_T` of `D(𝒪_{X_T})`. -/
theorem relativeDerivedHom_obj (f : X ⟶ Y) (K E : derivedModules B S hS X) (T : SchemesOver Y) :
    (relativeDerivedHom f K E).obj (Opposite.op T) =
      (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)).obj K ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)).obj E) :=
  rfl

end AlgebraicGeometry.Space
