module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.ContinuousActions
public import Mathlib.CategoryTheory.Galois.Equivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The forgetful functor on finite continuous actions

The forgetful functor from finite continuous actions of a topological group to finite sets is
the composition of the inclusion of the subcategory with the forgetful functor on all finite
actions, and composing it with the inclusion of finite sets into sets gives the underlying-set
functor. These identifications are all identities on objects, so each is given by refl
components; they are recorded as isomorphisms of functors because the two sides are not
syntactically equal. From them the forgetful functor inherits preservation and reflection of
finite limits and finite colimits.

## Main definitions

* `CategoryTheory.forget₂InclIso` identifies the forgetful functor followed by the inclusion of
  finite sets with the underlying-set functor.
* `CategoryTheory.contActionForgetFinIso` identifies the forgetful functor with the inclusion of
  the subcategory followed by the forgetful functor on all finite actions.
* `CategoryTheory.restrictionForgetFinIso` identifies restriction along a continuous
  homomorphism followed by forgetting with forgetting.
* `CategoryTheory.actionForgetFinIso` identifies the canonical functor to finite continuous
  actions of the automorphism group, followed by forgetting, with the original fibre functor.

## Main results

* `CategoryTheory.contAction_forget_preservesFiniteLimits`,
  `CategoryTheory.contAction_forget_preservesFiniteColimits`,
  `CategoryTheory.contAction_forget_reflectsFiniteLimits` and
  `CategoryTheory.contAction_forget_reflectsFiniteColimits` record exactness of the forgetful
  functor and the fact that it reflects finite limits and colimits.

## References

* [Stacks Project, Tag 0BN5](https://stacks.math.columbia.edu/tag/0BN5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped FintypeCatDiscrete

universe u v w

namespace CategoryTheory

/-- The canonical functor from a Galois category to finite continuous actions of the
automorphism group of a fibre functor, followed by forgetting the action, is the fibre
functor. -/
@[sga "1 V 5.1" "partial"]
public def actionForgetFinIso {C : Type u} [Category.{v} C]
    (F : C ⥤ FintypeCat.{w}) :
    PreGaloisCategory.functorToContAction F ⋙
      forget₂ (ContAction FintypeCat.{w} (Aut F)) FintypeCat ≅ F := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  rfl

/-- Forgetting the action of a finite continuous action and then including finite sets into
sets is the underlying-set functor. -/
public def forget₂InclIso {G : Type*} [Group G] [TopologicalSpace G] :
    forget₂ (ContAction FintypeCat.{w} G) FintypeCat ⋙ FintypeCat.incl ≅
      forget (ContAction FintypeCat.{w} G) := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  rfl

/-- Forgetting the action of a finite continuous action is the inclusion of the subcategory of
continuous actions followed by forgetting the action of a finite action. -/
public def contActionForgetFinIso {G : Type*} [Group G] [TopologicalSpace G] :
    forget₂ (ContAction FintypeCat.{w} G) FintypeCat ≅
      ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{w}) (G := G)) ⋙
        Action.forget FintypeCat.{w} G := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  rfl

/-- Forgetting the action of a finite continuous action preserves finite limits. -/
public instance contAction_forget_preservesFiniteLimits
    {G : Type*} [Group G] [TopologicalSpace G] :
    PreservesFiniteLimits (forget₂ (ContAction FintypeCat.{w} G) FintypeCat) := by
  let : PreservesFiniteLimits
      (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{w}) (G := G)) ⋙
        Action.forget FintypeCat.{w} G) := comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (contActionForgetFinIso (G := G)).symm

/-- Forgetting the action of a finite continuous action preserves finite colimits. -/
public instance contAction_forget_preservesFiniteColimits
    {G : Type*} [Group G] [TopologicalSpace G] :
    PreservesFiniteColimits (forget₂ (ContAction FintypeCat.{w} G) FintypeCat) := by
  let : PreservesFiniteColimits
      (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{w}) (G := G)) ⋙
        Action.forget FintypeCat.{w} G) := comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (contActionForgetFinIso (G := G)).symm

/-- Forgetting the action of a finite continuous action reflects finite limits. -/
public instance contAction_forget_reflectsFiniteLimits
    {G : Type*} [Group G] [TopologicalSpace G] :
    ReflectsFiniteLimits (forget₂ (ContAction FintypeCat.{w} G) FintypeCat) where
  reflects J _ _ := by
    let : ReflectsLimitsOfShape J
        (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{w}) (G := G)) ⋙
          Action.forget FintypeCat.{w} G) := by infer_instance
    exact reflectsLimitsOfShape_of_natIso (contActionForgetFinIso (G := G)).symm

/-- Forgetting the action of a finite continuous action reflects finite colimits. -/
public instance contAction_forget_reflectsFiniteColimits
    {G : Type*} [Group G] [TopologicalSpace G] :
    ReflectsFiniteColimits (forget₂ (ContAction FintypeCat.{w} G) FintypeCat) where
  reflects J _ _ := by
    let : ReflectsColimitsOfShape J
        (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{w}) (G := G)) ⋙
          Action.forget FintypeCat.{w} G) := by infer_instance
    exact reflectsColimitsOfShape_of_natIso (contActionForgetFinIso (G := G)).symm

/-- Restricting a finite continuous action along a continuous homomorphism does not change its
underlying finite set. -/
public def restrictionForgetFinIso {G' G : Type*} [Group G'] [Group G]
    [TopologicalSpace G'] [TopologicalSpace G] (h : G' →ₜ* G) :
    ContAction.res FintypeCat h ⋙ forget₂ (ContAction FintypeCat G') FintypeCat ≅
      forget₂ (ContAction FintypeCat G) FintypeCat := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  rfl

end CategoryTheory
