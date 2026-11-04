module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAb

/-!
# Compatibility (b) of Stacks 0D70 for the inverse image of abelian sheaves

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
For a sheaf of sets `𝒢` on `(D, K)` the library already identifies the restriction of `a⁻¹𝒢` to
the component of simplicial degree `n` with `a_n⁻¹𝒢`: that is
`CategoryTheory.SimplicialSiteSituation.Augmentation.componentRestrictionIso`, in functorial
form `restrictCompInverseImageIso`, tagged as compatibility (b) of Stacks 0D70 in inverse
images.

This file supplies the same identification for *abelian* sheaves: the restriction
`CategoryTheory.SimplicialSiteSituation.abelianComponent` of the abelian inverse image
`totalInverseImageAb` along the total augmentation is the abelian inverse image
`componentInverseImageAb` along the augmentation of the degree.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentRestrictionAbInverseImageNatIso`: the
  comparison as an isomorphism of functors `Sheaf K Ab ⥤ Sheaf (S.componentTopology n) Ab`,
  hence natural in the abelian sheaf on the augmentation site.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionAbInverseImageIso`: its value at
  an abelian sheaf `G`.

## Main results

* `CategoryTheory.SimplicialSiteSituation`
  `.sheafCompose_forget_map_componentRestrictionAbInverseImageIso_hom`: forgetting the group
  operations, the comparison *is* the set-level comparison `componentRestrictionIso` of
  Stacks 0D70, compatibility (b).

## Implementation notes

Both inverse images are `CategoryTheory.Sites.abelianInverseImage` of a morphism of topoi, which
is `Functor.mapCommGrp` of the geometric inverse image conjugated by the equivalence of
Stacks 04JC between abelian sheaves and commutative group objects. So the comparison is built by
conjugating the *set-level* comparison `totalMorphismOfTopoi_restrict_iso`, rather than by taking
mates of a direct-image comparison: `Functor.mapCommGrpCompIso` splits the inverse image of the
composite, `Functor.mapCommGrpNatIso` transports the set-level comparison to group objects, the
Stacks 00YT comparison `componentRestrictionAbIso` replaces the restriction of abelian sheaves by
`mapCommGrp` of the restriction of sheaves of sets, and the counit
`Sites.AbelianSheaf.externalInternalIso` cancels the equivalence in the middle. Because every
step forgets to an identity, the underlying map of sheaves of sets is the set-level comparison
on the nose, which is what the final theorem records with a single `rfl`.

As in `StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationComponentPushforwardAb.lean`, the
monoidal, braided and finite-limit instances of `Stacks.Sites.AbelianPullback` are reused by name
rather than redeclared: `componentRestrictionAbIso` was elaborated with those terms, and with the
braided structure of the restriction obtained by a different route the comparisons no longer
unify. For the same reason the restriction of sheaves of sets is spelled `restrictSets`.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
namespace CategoryTheory.SimplicialSiteSituation

namespace Augmentation

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.braidedSheafToPresheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Functor.Braided.ofChosenFiniteProducts

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- The geometric inverse image of the total augmentation preserves finite limits. -/
noncomputable local instance preservesFiniteLimitsTotalInverseImage :
    PreservesFiniteLimits (totalMorphismOfTopoi S D K a).inverseImage :=
  (totalMorphismOfTopoi S D K a).preservesFiniteLimits

/-- The geometric inverse image of the augmentation of a degree preserves finite limits. -/
noncomputable local instance preservesFiniteLimitsComponentInverseImage :
    PreservesFiniteLimits (componentAugmentation S D K a n).inverseImage :=
  (componentAugmentation S D K a n).preservesFiniteLimits

/-- **Stacks 0D70, compatibility (b), in inverse images**, with the restriction of sheaves of
sets spelled as the direct image along the component inclusion. -/
def restrictSetsCompInverseImageIso :
    (totalMorphismOfTopoi S D K a).inverseImage ⋙ restrictSets S n ≅
      (componentAugmentation S D K a n).inverseImage :=
  totalMorphismOfTopoi_restrict_iso S D K a n

/-- **Stacks 0D70, compatibility (b)** on commutative group objects: applying the inverse image
of the total augmentation to a commutative group object and restricting the result to the
component of simplicial degree `n` is applying the inverse image of the augmentation of that
degree. -/
def restrictSetsCompInverseImageGrpIso :
    (totalMorphismOfTopoi S D K a).inverseImage.mapCommGrp ⋙ (restrictSets S n).mapCommGrp ≅
      (componentAugmentation S D K a n).inverseImage.mapCommGrp :=
  (Functor.mapCommGrpCompIso (F := (totalMorphismOfTopoi S D K a).inverseImage)
      (G := restrictSets S n)).symm ≪≫
    Functor.mapCommGrpNatIso (restrictSetsCompInverseImageIso S D K a n)

/-- **Stacks 0D70, compatibility (b), for the inverse image of abelian sheaves**, with both
inverse images unfolded through the equivalence of Stacks 04JC between abelian sheaves and
commutative group objects. -/
def totalInverseImageAbCompRestrictionIso :
    (Sites.AbelianSheaf.internalSheaf K ⋙
        (totalMorphismOfTopoi S D K a).inverseImage.mapCommGrp ⋙
          Sites.AbelianSheaf.externalSheaf S.totalTopology) ⋙
        restrictAb S n ≅
      Sites.AbelianSheaf.internalSheaf K ⋙
        (componentAugmentation S D K a n).inverseImage.mapCommGrp ⋙
          Sites.AbelianSheaf.externalSheaf (S.componentTopology n) :=
  Functor.isoWhiskerLeft _ (componentRestrictionAbIso S n).symm ≪≫
    Functor.isoWhiskerLeft
      (Sites.AbelianSheaf.internalSheaf K ⋙
        (totalMorphismOfTopoi S D K a).inverseImage.mapCommGrp)
      (Functor.isoWhiskerRight
        (Sites.AbelianSheaf.externalInternalIso S.totalTopology)
        ((restrictSets S n).mapCommGrp ⋙
          Sites.AbelianSheaf.externalSheaf (S.componentTopology n))) ≪≫
    Functor.isoWhiskerLeft (Sites.AbelianSheaf.internalSheaf K)
      (Functor.isoWhiskerRight (restrictSetsCompInverseImageGrpIso S D K a n)
        (Sites.AbelianSheaf.externalSheaf (S.componentTopology n)))

end Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- **The abelian analogue of Stacks 0D70, compatibility (b), in inverse images.** Restricting
the inverse image `a⁻¹𝒢` of an abelian sheaf along the total augmentation to the component of
simplicial degree `n` is the inverse image `a_n⁻¹𝒢` along the augmentation of that degree,
naturally in `𝒢`. -/
def componentRestrictionAbInverseImageNatIso :
    Augmentation.totalInverseImageAb S D K a ⋙ S.abelianComponent n ≅
      Augmentation.componentInverseImageAb S D K a n :=
  Augmentation.totalInverseImageAbCompRestrictionIso S D K a n

/-- **The abelian analogue of Stacks 0D70, compatibility (b), in inverse images.** Restricting
the inverse image `a⁻¹𝒢` of an abelian sheaf along the total augmentation to the component of
simplicial degree `n` is the inverse image `a_n⁻¹𝒢` along the augmentation of that degree,
naturally in `𝒢`. -/
def componentRestrictionAbInverseImageNatIso' :
    Augmentation.totalInverseImageAb S D K a ⋙ S.restrictAb n ≅
      Augmentation.componentInverseImageAb S D K a n :=
  Augmentation.totalInverseImageAbCompRestrictionIso S D K a n

/-- **The abelian analogue of Stacks 0D70, compatibility (b), in inverse images.** Restricting
the inverse image `a⁻¹𝒢` of an abelian sheaf along the total augmentation to the component of
simplicial degree `n` gives the inverse image `a_n⁻¹𝒢` along the augmentation of that degree. -/
def componentRestrictionAbInverseImageIso (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : Augmentation S D K) (G : Sheaf K Ab.{u})
    (n : SimplexCategory) :
    (S.abelianComponent n).obj ((Augmentation.totalInverseImageAb S D K a).obj G) ≅
      (Augmentation.componentInverseImageAb S D K a n).obj G :=
  (componentRestrictionAbInverseImageNatIso S D K a n).app G

/-- **The abelian analogue of Stacks 0D70, compatibility (b), in inverse images.** Restricting
the inverse image `a⁻¹𝒢` of an abelian sheaf along the total augmentation to the component of
simplicial degree `n` gives the inverse image `a_n⁻¹𝒢` along the augmentation of that degree. -/
def componentRestrictionAbInverseImageIso' (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : Augmentation S D K) (G : Sheaf K Ab.{u})
    (n : SimplexCategory) :
    (S.restrictAb n).obj ((Augmentation.totalInverseImageAb S D K a).obj G) ≅
      (Augmentation.componentInverseImageAb S D K a n).obj G :=
  (componentRestrictionAbInverseImageNatIso' S D K a n).app G

/-- The comparison is the set-level comparison of Stacks 0D70, compatibility (b): forgetting the
group operations on both sides, the isomorphism is `componentRestrictionIso` of the underlying
sheaf of sets. -/
theorem sheafCompose_forget_map_componentRestrictionAbInverseImageIso_hom
    (G : Sheaf K Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        (componentRestrictionAbInverseImageIso S D K a G n).hom =
      (Augmentation.componentRestrictionIso S D K a
        ((sheafCompose K (forget Ab.{u})).obj G) n).hom :=
  rfl

end CategoryTheory.SimplicialSiteSituation
end
