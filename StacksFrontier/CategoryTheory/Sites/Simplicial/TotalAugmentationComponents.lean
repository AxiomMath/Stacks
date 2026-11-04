module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentation

/-!
# The total augmentation against the components, in the cocontinuous case

In the cocontinuous form of the simplicial-site situation the augmentation of the total site is
the morphism of topoi induced by the cocontinuous functor out of the total category. This file
compares it with the morphisms of topoi of the individual simplicial degrees: composing the
inclusion of a component with the total augmentation gives the augmentation of that component,
in direct images and in inverse images alike. The comparison supplies a canonical map from the
total direct image to the direct image of each component, and the direct images of the
components carry a transition map for every simplex map.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalComponentUnitMap`: the canonical
  map from the total direct image to the direct image of a component, obtained from the
  adjunction unit of the component inclusion.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentDirectImageTransitionMap`:
  the transition on the direct images of the components induced by a simplex map.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.vertexDirectImageMap`: that transition
  at a vertex of the one-simplex.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentInclusionCompPushforwardIso`:
  composing the inclusion of a component with the total augmentation agrees with the
  augmentation of that component, as an isomorphism of direct images.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentInclusionCompInverseImageIso`:
  the same comparison in inverse images, so the restriction to a component of the inverse image
  of a sheaf on the augmentation site is its inverse image along the component augmentation.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_map_ιNatTrans`
  and `.isIso_totalAugmentationFunctor_map_ιNatTrans`: the functor out of the total category
  sends a cross-fibre arrow of the total category to a transport along an equality of functors,
  hence to an isomorphism.

## Implementation notes

An equality of morphisms of topoi is expressed, here as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationPushforward.lean`, as a natural
isomorphism of direct-image functors: the functors obtained by composing adjunctions are not
definitionally equal. The inverse-image comparison is then not an independent construction but
the comparison of two left adjoints of the same right adjoint, so it costs nothing beyond
uniqueness of adjoints and needs no coherence of its own.

The component of a sheaf on the total site is written as the inverse image along the morphism
of topoi of the component inclusion rather than as the restriction functor, since that is the
form in which the adjunction unit is available; the two are identified by Mathlib's
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, which is also
how the transition map converts the inverse-image transition of a restriction into a map
between the components in this form. No second name is introduced for that identification.

The cross-fibre arrows of the total category are Mathlib's `CategoryTheory.Grothendieck.ιNatTrans`,
and the total functor sends them to transports along the compatibility equality of the
augmentation, because it is assembled by `CategoryTheory.Grothendieck.functorFromOfEq` from
fibrewise data whose transitions are those transports. That is the precise sense in which the
augmentation does not see the simplicial direction.

The direct-image comparison below is deliberately NOT called `totalComponentPushforwardIso`,
which is the name of the general notion for this tag. The statement here is the case-(B) half
only, and it is about the
morphism of topoi of the cocontinuous functor out of the total category rather than about an
augmentation of an arbitrary simplicial-site situation; a declaration carrying that name
and stating something weaker would be a shadow of it.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace CocontinuousSimplicialSite

universe u

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-- The simplicial-site situation of case (B) attached to a cocontinuous simplicial site. -/
abbrev situation (C : CocontinuousSimplicialSite.{u}) : SimplicialSiteSituation.{u} :=
  ⟨Sum.inr C⟩

namespace Augmentation

variable (a : C.Augmentation D K)

/-- **Stacks 0D70, compatibility (2), case (B).** Composing the inclusion of a component with
the total augmentation gives the augmentation of that component, as an isomorphism of direct
images. -/
def componentInclusionCompPushforwardIso (n : SimplexCategory) :
    (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward ⋙
        (totalMorphismOfTopoi a).pushforward ≅
      (SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a n).pushforward :=
  componentPushforwardCompIso a (Opposite.op n)

/-- **Stacks 0D70, compatibility (2), case (B), in inverse images.** The restriction to a
component of the inverse image of a sheaf on the augmentation site is its inverse image along
the augmentation of that component. The two functors are left adjoints of the two direct images
compared by `componentInclusionCompPushforwardIso`, so this is uniqueness of adjoints. -/
def componentInclusionCompInverseImageIso (n : SimplexCategory) :
    (totalMorphismOfTopoi a).inverseImage ⋙
        (SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage ≅
      (SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a n).inverseImage :=
  Adjunction.leftAdjointUniq
    ((totalMorphismOfTopoi a).comp
      (SimplicialSiteSituation.componentMorphism (situation C) n)).adj
    (((SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a n).adj).ofNatIsoRight (componentInclusionCompPushforwardIso a n).symm)

/-- The canonical map from the total direct image to the direct image of a component, obtained
from the adjunction unit of the component inclusion and the comparison
`componentInclusionCompPushforwardIso`. -/
def totalComponentUnitMap (F : Sheaf (situation C).totalTopology (Type u))
    (n : SimplexCategory) :
    (totalMorphismOfTopoi a).pushforward.obj F ⟶
      (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a n).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F) :=
  (totalMorphismOfTopoi a).pushforward.map
      ((SimplicialSiteSituation.componentMorphism (situation C) n).adj.unit.app F) ≫
    (componentInclusionCompPushforwardIso a n).hom.app
      ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F)

/-- The transition on the direct images of the components induced by a simplex map: the mate of
the inverse-image transition of the restrictions under the adjunction of the simplicial
transition, followed by the comparison of the component augmentations. -/
def componentDirectImageTransitionMap (F : Sheaf (situation C).totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a m).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) m).inverseImage.obj F) ⟶
      (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a n).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F) := by
  let f := (situation C).transitionMorphism φ
  let e (k : SimplexCategory) :
      (SimplicialSiteSituation.componentMorphism (situation C) k).inverseImage.obj F ≅
        ((situation C).restrict k).obj F :=
    (((situation C).inclusion k).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type u) ((situation C).componentTopology k) (situation C).totalTopology).app F
  exact (SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a m).pushforward.map
      (f.adj.homEquiv _ _
        (f.inverseImage.map (e m).hom ≫
          ((situation C).fiberTransition φ).app F ≫ (e n).inv)) ≫
    (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ).hom.app
      ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F)

/-- The transition on direct images at a vertex of the one-simplex. These are the two maps whose
equalizer Stacks 0D70 (3) asserts the total direct image to be. -/
def vertexDirectImageMap (F : Sheaf (situation C).totalTopology (Type u)) (i : Fin 2) :=
  componentDirectImageTransitionMap a F
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)

/-- The functor out of the total category sends a cross-fibre arrow to the transport along the
compatibility equality of the augmentation: the augmentation does not see the simplicial
direction. -/
theorem totalAugmentationFunctor_map_ιNatTrans {c c' : SimplexCategoryᵒᵖ} (f : c ⟶ c')
    (x : C.underlying.obj c) :
    (totalAugmentationFunctor a).map ((Grothendieck.ιNatTrans f).app x) =
      (eqToHom (totalAugmentationFibre_eq a f)).app x :=
  Grothendieck.functorFromOfEq_map_ιNatTrans_app _ _ _ _ f x

/-- The functor out of the total category inverts the cross-fibre arrows of the total
category. -/
instance isIso_totalAugmentationFunctor_map_ιNatTrans {c c' : SimplexCategoryᵒᵖ} (f : c ⟶ c')
    (x : C.underlying.obj c) :
    IsIso ((totalAugmentationFunctor a).map ((Grothendieck.ιNatTrans f).app x)) := by
  rw [totalAugmentationFunctor_map_ιNatTrans]
  exact inferInstanceAs (IsIso ((eqToIso (totalAugmentationFibre_eq a f)).hom.app x))

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end
