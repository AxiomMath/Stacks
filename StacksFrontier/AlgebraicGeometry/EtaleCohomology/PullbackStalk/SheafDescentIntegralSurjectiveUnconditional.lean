module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperSurjectiveUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent for small étale sheaves along an integral surjection

Let `f : X ⟶ Y` be a surjective integral morphism of schemes. [Stacks, Tag 0GEZ] says that the
functor sending a sheaf on the small étale site of `Y` to its canonical descent datum for
`{X ⟶ Y}` is an equivalence of categories. This file proves it for the library's descent functor
`AlgebraicGeometry.smallEtaleSheafDescentFunctor`, with no hypothesis beyond those of the source,
as an input of [Stacks, Tag 0GF1].

The statement proved here is that of the base declaration
`AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral`; nothing
here carries a Stacks attribute.

## Main results

* `AlgebraicGeometry.isEquivalence_smallEtaleSheafDescentFunctor_iff`: the library's descent
  functor is an equivalence exactly when the descent functor of the explicit pseudofunctor
  `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor` is.
* `smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective`:
  [Stacks, Tag 0GEZ] for the explicit pseudofunctor.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective`:
  the content of [Stacks, Tag 0GEZ].

## Implementation notes

The source's proof is the reduction to geometric points of [Stacks, Tag 0GEZ], with the
integral base change theorem [Stacks, Tag 0EYP] as its input. Here the descent argument is
`smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans`,
which needs the base change theorem only for two cartesian squares with an integral right-hand
side, and [Stacks, Tag 0EYP] at set coefficients is
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom`.

## References

* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The library's small étale sheaf descent functor is an equivalence exactly when the descent
functor of the explicit pseudofunctor of small étale sheaves and their inverse images is. -/
theorem isEquivalence_smallEtaleSheafDescentFunctor_iff (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence ↔
      (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence := by
  have key : ∀ P, P = smallEtaleSheafInverseImagePseudofunctor B →
      ((P.toDescentData (fun _ : Unit ↦ f)).IsEquivalence ↔
        (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence) := by
    rintro _ rfl
    exact Iff.rfl
  rw [← key _ (smallEtaleSheafPullbackSystem_pseudofunctor_eq B)]
  have : (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor.IsEquivalence := by
    have gen : ∀ {A A' : Cat.{u + 1, u + 2}} (h : A = A'), (eqToHom h).toFunctor.IsEquivalence := by
      rintro A _ rfl
      exact (inferInstance : (𝟭 A).IsEquivalence)
    exact gen _
  unfold smallEtaleSheafDescentFunctor
  exact ⟨fun _ ↦ Functor.isEquivalence_of_comp_left
    (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor _,
    fun _ ↦ inferInstance⟩

/-- **Effective descent of small étale sheaves along an integral surjection**, for the explicit
pseudofunctor of small étale sheaves and their inverse images. -/
@[sga "4 VIII 9.4"]
theorem smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsIntegralHom (B.inclusion.map f)] :
    (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  let XX := ChosenPullback.ofHasPullback f f
  let ZZ := ChosenPullback.ofHasPullback XX.p f
  have h₁ : IsIntegralHom (B.inclusion.map XX.p₁) :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom)
      (B.inclusion.map_isPullback XX.isPullback.flip) ‹_›
  have hp : IsIntegralHom (B.inclusion.map XX.p) := by
    rw [← XX.hp₁, B.inclusion.map_comp]
    infer_instance
  exact
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans
      B f (B.inclusion.map f).surjective XX ZZ
      (fun M ↦ isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom B XX.p₁ XX.p₂ f f
        (B.inclusion.map_isPullback XX.isPullback) XX.condition M)
      (fun N ↦ isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom B ZZ.p₁ ZZ.p₂ XX.p f
        (B.inclusion.map_isPullback ZZ.isPullback) ZZ.condition N)

/-- **Effective descent of small étale sheaves along an integral surjection.** For a surjective
integral morphism `f : X ⟶ Y` of a big étale site, the functor sending a sheaf of sets on the
small étale site of `Y` to its canonical descent datum for `{X ⟶ Y}` is an equivalence of
categories.

This is the content of [Stacks, Tag 0GEZ], also stated in the module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjective`.
-/
@[sga "4 VIII 9.4"]
theorem smallEtaleSheafDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsIntegralHom (B.inclusion.map f)] :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  (isEquivalence_smallEtaleSheafDescentFunctor_iff B f).2
    (smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective B f)

end AlgebraicGeometry

end
