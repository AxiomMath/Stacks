module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjective
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjective

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChangeUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChangeUnconditional

/-!
# Étale descent along surjective integral morphisms

Let `f : X ⟶ Y` be a surjective integral morphism of a big étale site. Sheaves of sets on the small
étale site of `Y` are equivalent to descent data for `{X ⟶ Y}`.

## Main results

* `smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral_unconditional`:
  the functor from sheaves of sets on the small étale site of `Y` to descent data for `{X ⟶ Y}` is
  an equivalence of categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be a surjective integral morphism of a big étale site. The functor from sheaves
of sets on the small étale site of `Y` to descent data for `{X ⟶ Y}` is an equivalence of
categories. -/
@[stacks 0GEZ "The functor is the canonical descent functor
`AlgebraicGeometry.smallEtaleSheafDescentFunctorGeneral`, sending a sheaf on `Y_etale` to its
inverse image on `X_etale` with the canonical descent isomorphism. Sheaves take values in
`Type (u + 1)`, the universe of the big étale site. Proved from the base-change isomorphism for
small étale sheaves along integral morphisms [Stacks, Tag 0EYP], applied to `X ×_Y X ⟶ X` and to
`X ×_Y X ×_Y X ⟶ X ×_Y X`."]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_integral_unconditional
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsIntegralHom (B.inclusion.map f)] :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  let XX := ChosenPullback.ofHasPullback f f
  let ZZ := ChosenPullback.ofHasPullback XX.p f
  have h₁ : IsIntegralHom (B.inclusion.map XX.p₁) :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom)
      (B.inclusion.map_isPullback XX.isPullback.flip) ‹_›
  have hp : IsIntegralHom (B.inclusion.map XX.p) := by
    rw [← XX.hp₁, B.inclusion.map_comp]
    infer_instance
  exact smallEtaleSheafDescentFunctor_isEquivalence_of_isIso_smallEtaleBaseChangeNatTrans B f
    (B.inclusion.map f).surjective XX ZZ
    (fun M ↦ isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ.{0} B XX.p₁ XX.p₂ f f
      (B.inclusion.map_isPullback XX.isPullback) XX.condition M)
    (fun N ↦ isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ.{0} B ZZ.p₁ ZZ.p₂ XX.p f
      (B.inclusion.map_isPullback ZZ.isPullback) ZZ.condition N)

end AlgebraicGeometry

end
