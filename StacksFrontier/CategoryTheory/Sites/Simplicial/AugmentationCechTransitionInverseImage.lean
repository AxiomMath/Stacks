module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.PushPullTransition

/-!
# The cosimplicial transition of the Čech diagram at an inverse image

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The cosimplicial sheaf of Stacks 0D70, compatibility (c), has
degree-`n` term `F ↦ a_{n,*}F_n` and its transition at a simplex map `φ : m ⟶ n` is
`CategoryTheory.SimplicialSiteSituation.Augmentation.componentPushforwardTransition`, built from
the direct-image transition of the restrictions and Stacks 0D70, compatibility (1).

At `F = a^{-1}𝒢` the restrictions are the inverse images along the component augmentations, by
Stacks 0D70, compatibility (b), and this module computes the transition through that
identification: it becomes the direct-image form of the inverse-image comparison of the component
augmentations (Stacks 0D70, compatibility (2)) followed by compatibility (1). This is the push-pull
transition of the factorization formed by the component augmentations and the simplicial transition
between their sources.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.componentPushforwardTransition_app_inverseImage`: the degreewise identity.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.restrictCompInverseImageIso_componentPushforwardTransition`: the same as an identity of
  natural transformations of functors of the sheaf on the augmentation site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionDirectInverseImageTrans_eq`:
  the direct-image form of compatibility (2) is the unit of the simplicial transition followed by
  compatibility (2) itself.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.pushPullTransition_componentAugmentation`:
  the transition is the push-pull transition of the factorization of compatibility (1).

## Implementation notes

Both sides are stated with the inverse image of the morphism of topoi of Stacks 0D70, part (2):
the uniform reading of the total augmentation, whose direct image is a limit over the simplex
category.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The cosimplicial transition of the Čech diagram of Stacks 0D79 at `a^{-1}𝒢`.** Read through
the identification of the restrictions of `a^{-1}𝒢` with the inverse images along the component
augmentations, it is the direct-image form of the inverse-image comparison of those augmentations
followed by the comparison of Stacks 0D70, compatibility (1). -/
theorem componentPushforwardTransition_app_inverseImage (G : Sheaf K (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentPushforwardTransition S D K a φ).app (inverseImageSheaf S D K a G) ≫
        (componentAugmentation S D K a n).pushforward.map
          (componentRestrictionIso S D K a G n).hom =
      (componentAugmentation S D K a m).pushforward.map
          ((componentRestrictionIso S D K a G m).hom ≫
            (transitionDirectInverseImageTrans S D K a φ).app G) ≫
        (transitionPushforwardIso S D K a φ).hom.app
          ((componentAugmentation S D K a n).inverseImage.obj G) := by
  have hnat := (transitionPushforwardIso S D K a φ).hom.naturality
    (componentRestrictionIso S D K a G n).hom
  dsimp only [Functor.comp_map] at hnat
  have hchange : (componentPushforwardTransition S D K a φ).app
        (inverseImageSheaf S D K a G) =
      (componentAugmentation S D K a m).pushforward.map
          ((S.restrictTransition φ).app (inverseImageSheaf S D K a G)) ≫
        (transitionPushforwardIso S D K a φ).hom.app
          ((S.restrict n).obj (inverseImageSheaf S D K a G)) := rfl
  rw [hchange, Category.assoc, ← hnat, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← componentRestrictionIso_restrictTransition S D K a G φ]

/-- **The cosimplicial transition of the Čech diagram of Stacks 0D79 at an inverse image, as an
identity of natural transformations.** The transition of the cosimplicial sheaf of Stacks 0D70,
compatibility (c), whiskered with the inverse image of the total augmentation, is carried by the
identifications of compatibility (b) to the composite of compatibility (2) in direct-image form
with compatibility (1). -/
theorem restrictCompInverseImageIso_componentPushforwardTransition
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.whiskerLeft (inverseImage S D K a) (componentPushforwardTransition S D K a φ) ≫
        (Functor.isoWhiskerRight (restrictCompInverseImageIso S D K a n)
          (componentAugmentation S D K a n).pushforward).hom =
      (Functor.isoWhiskerRight (restrictCompInverseImageIso S D K a m)
            (componentAugmentation S D K a m).pushforward).hom ≫
        Functor.whiskerRight (transitionDirectInverseImageTrans S D K a φ)
            (componentAugmentation S D K a m).pushforward ≫
          Functor.whiskerLeft (componentAugmentation S D K a n).inverseImage
            (transitionPushforwardIso S D K a φ).hom := by
  refine NatTrans.ext (funext fun G => ?_)
  have h := componentPushforwardTransition_app_inverseImage S D K a G φ
  rwa [CategoryTheory.Functor.map_comp, Category.assoc] at h

/-- **The direct-image form of the inverse-image comparison of Stacks 0D70, compatibility (2), is
the unit of the simplicial transition followed by that comparison.** -/
theorem transitionDirectInverseImageTrans_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionDirectInverseImageTrans S D K a φ =
      Functor.whiskerLeft (componentAugmentation S D K a m).inverseImage
          (S.transitionMorphism φ).adj.unit ≫
        Functor.whiskerRight (transitionInverseImageIso S D K a φ).hom
          (S.transitionMorphism φ).pushforward :=
  rfl

/-- **The cosimplicial transition of the Čech diagram at an inverse image is the push-pull
transition of the factorization of Stacks 0D70, compatibility (1).** The degree-`m` and degree-`n`
component augmentations and the simplicial transition between their sources form a factorization of
morphisms of topoi, with `transitionPushforwardIso` its comparison of direct images, and its
push-pull transition is the direct-image form of compatibility (2) followed by compatibility (1).
-/
theorem pushPullTransition_componentAugmentation {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoi.pushPullTransition (componentAugmentation S D K a m)
        (componentAugmentation S D K a n) (S.transitionMorphism φ)
        (transitionPushforwardIso S D K a φ) =
      Functor.whiskerRight (transitionDirectInverseImageTrans S D K a φ)
          (componentAugmentation S D K a m).pushforward ≫
        Functor.whiskerLeft (componentAugmentation S D K a n).inverseImage
          (transitionPushforwardIso S D K a φ).hom := by
  refine NatTrans.ext (funext fun G => ?_)
  rw [MorphismOfTopoi.pushPullTransition_app]
  change _ = (componentAugmentation S D K a m).pushforward.map
      ((transitionDirectInverseImageTrans S D K a φ).app G) ≫
    (transitionPushforwardIso S D K a φ).hom.app
      ((componentAugmentation S D K a n).inverseImage.obj G)
  rw [transitionDirectInverseImageTrans_eq, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
