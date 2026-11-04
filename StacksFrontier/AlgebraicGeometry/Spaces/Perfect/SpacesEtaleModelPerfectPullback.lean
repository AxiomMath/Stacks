module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedPullbackPerfectGeneralUniverse

/-!
# Derived pullback of perfect objects on the spaces-étale models

Let `f : X ⟶ Y` be a morphism of algebraic spaces. The morphism of models of ringed
spaces-étale sites `AlgebraicGeometry.Space.spacesEtaleModelHom f` is presented by a morphism of
ringed sites, base change `V ↦ V ×_Y X` being a morphism of sites between categories with finite
limits that preserves them. Stacks 08H6 therefore applies: `Lf^*` sends perfect objects of
`D(𝒪_Y)` to perfect objects of `D(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelRingedSiteHom`: the morphism of ringed sites
  presenting `AlgebraicGeometry.Space.spacesEtaleModelHom f`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedPullback_spacesEtaleModelHom`: **Stacks 08H6** on the
  spaces-étale models.

## References

* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

/-- The model of the spaces-étale site of `X` has finite limits: the spaces-étale site has a
final object and fibre products, and the model is equivalent to it. -/
instance hasFiniteLimits_smallModel_spacesEtale (X : AlgebraicSpaces B S hS) :
    HasFiniteLimits (SmallModel.{u} (SpacesEtale B S hS X)) :=
  haveI : HasFiniteLimits (SpacesEtale B S hS X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence
    (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse⟩

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

variable (B S hS) in
/-- **The morphism of ringed sites presenting `AlgebraicGeometry.Space.spacesEtaleModelHom f`**:
base change on the models, a morphism of sites, with the structure map of the morphism of models.
-/
def spacesEtaleModelRingedSiteHom :
    RingedSite.Hom (spacesEtaleModelRingedSite B S hS X) (spacesEtaleModelRingedSite B S hS Y) where
  u := smallModelBaseChange B S hS f
  isMorphismOfSites := isMorphismOfSites_smallModelBaseChange B S hS f
  fsharp := (spacesEtaleModelHom B S hS f).fSharp

/-- The morphism of ringed sites presents the morphism of models. -/
theorem spacesEtaleModelRingedSiteHom_toRingedToposSiteHom :
    (spacesEtaleModelRingedSiteHom B S hS f).toRingedToposSiteHom = spacesEtaleModelHom B S hS f :=
  rfl

/-- **Stacks 08H6 on the spaces-étale models.** For a morphism `f : X ⟶ Y` of algebraic spaces,
derived pullback along the morphism of models `AlgebraicGeometry.Space.spacesEtaleModelHom f`
sends perfect objects of `D(𝒪_Y)` to perfect objects of `D(𝒪_X)`. -/
theorem isPerfect_derivedPullback_spacesEtaleModelHom
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y).O)))
    (hE : (spacesEtaleModelRingedSite B S hS Y).IsPerfect E) :
    (spacesEtaleModelRingedSite B S hS X).IsPerfect
      ((derivedPullback (spacesEtaleModelHom B S hS f)).obj E) :=
  have : PreservesFiniteLimits (spacesEtaleModelRingedSiteHom B S hS f).u :=
    inferInstanceAs (PreservesFiniteLimits (smallModelBaseChange B S hS f))
  RingedSite.Hom.isPerfect_derivedPullback_general (spacesEtaleModelRingedSiteHom B S hS f) E hE

end AlgebraicGeometry.Space

end
