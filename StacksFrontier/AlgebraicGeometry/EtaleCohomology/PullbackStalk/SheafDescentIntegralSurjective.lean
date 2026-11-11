module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange

/-!
# Effective descent for small étale sheaves along an integral surjection

For a morphism of schemes `f : X ⟶ Y` in a big étale site, descent of small étale sheaves is
effective along both projections which arise in the dévissage of descent along `f`: the
projection `X ×_Y X ⟶ X` is split by the diagonal, and the projection
`X ×_Y (X ×_Y X) ⟶ X ×_Y X` is split by the graph of the first projection. For an integral
surjection `f` these are exactly the two hypotheses of the base-change criterion of
[Stacks, Tag 0GF1] taken for the covering `f` itself, so an integral surjection satisfies every
hypothesis of that criterion.

## Main results

* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_self` and
  `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp`: the two
  split projections along which descent is effective.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral`: descent
  along an integral surjection is effective, given the dévissage of [Stacks, Tag 0GF1] as a
  hypothesis.

## Implementation notes

The last result takes the integral branch of the base-change criterion [Stacks, Tag 0GF1] as an
explicit hypothesis. The form of [Stacks, Tag 0GEZ] without that hypothesis is
`AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral_unconditional`
in `SheafDescentIntegralSurjectiveGeneral`, stated for the canonical descent functor
`AlgebraicGeometry.smallEtaleSheafDescentFunctorGeneral`.

## References

* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The diagonal splits the second projection `X ×_Y X ⟶ X`, so descent of small étale sheaves
is effective along it. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_self
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctor B (pullback.snd f f)).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_of_section B (pullback.snd f f)
    (pullback.lift (𝟙 X) (𝟙 X) rfl) (pullback.lift_snd _ _ _)

/-- The graph of the first projection splits the second projection
`X ×_Y (X ×_Y X) ⟶ X ×_Y X`, so descent of small étale sheaves is effective along it. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctor B
      (pullback.snd f (pullback.fst f f ≫ f))).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_of_section B
    (pullback.snd f (pullback.fst f f ≫ f))
    (pullback.lift (pullback.fst f f) (𝟙 _) (Category.id_comp _).symm)
    (pullback.lift_snd _ _ _)

/-- Descent of small étale sheaves along `f` is effective exactly when it is effective along the
structure morphism `X ×_Y X ⟶ Y`, the diagonal providing the required factorization. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_iff_pullback_fst_self_comp
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence ↔
      (smallEtaleSheafDescentFunctor B (pullback.fst f f ≫ f)).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_iff_baseChange B f f (𝟙 X) (Category.id_comp f)

/-- An integral surjection is an effective descent morphism for small étale sheaves. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsIntegralHom (B.inclusion.map f)]
    (devissage : ∀ {X' Y' Z' : B.Scheme} (f' : X' ⟶ Y') (g' : Z' ⟶ Y'),
      Surjective (B.inclusion.map g') → IsIntegralHom (B.inclusion.map g') →
      (smallEtaleSheafDescentFunctor B (pullback.snd f' g')).IsEquivalence →
      (smallEtaleSheafDescentFunctor B
        (pullback.snd f' (pullback.fst g' g' ≫ g'))).IsEquivalence →
      (smallEtaleSheafDescentFunctor B f').IsEquivalence) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  devissage f f ‹Surjective (B.inclusion.map f)› ‹IsIntegralHom (B.inclusion.map f)›
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_self B f)
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp B f)

end AlgebraicGeometry

end
