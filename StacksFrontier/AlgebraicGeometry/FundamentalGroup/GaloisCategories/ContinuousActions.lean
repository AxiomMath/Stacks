module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.FullSubcategory
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.Topology.Category.FinTopCat

/-!
# Finite continuous actions of a topological group form a Galois subcategory

Let `G` be a topological group. Continuity of an action of `G` on a finite discrete set is
detected orbitwise, and it is inherited by subobjects, by finite limits and by arbitrary
colimits inside the category of all finite `G`-sets. Consequently the finite continuous
`G`-sets form a Galois subcategory of the finite `G`-sets, and the forgetful functor to finite
sets is a fibre functor.

## Main results

* `Topology.continuous_of_injective_discrete` deduces continuity of a map from continuity of
  its composite with an injection into a discrete space.
* `CategoryTheory.action_continuous_of_orbits` reduces continuity of an action on a finite
  discrete set to continuity of each orbit map.
* `CategoryTheory.action_continuous_of_injective` transports continuity along an injective
  morphism of actions.
* `CategoryTheory.continuous_closed_limits` and `CategoryTheory.continuous_closed_colimits`
  say that continuity is closed under finite limits and under colimits.
* The remaining instances exhibit the finite continuous `G`-sets as a Galois subcategory with
  fibre functor the forgetful functor to `FintypeCat`.

## Implementation notes

A finite `G`-set carries the discrete topology, so every map out of it is continuous and the
content of continuity of the action is continuity of the orbit maps `g ↦ g • x`. This is what
makes all the closure properties elementary.

## References

* [Stacks Project, Tag 0BMV](https://stacks.math.columbia.edu/tag/0BMV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped FintypeCatDiscrete

universe u v

namespace Topology

/-- A map into a space that injects continuously into a discrete space is continuous as soon as
the composite is. -/
public lemma continuous_of_injective_discrete {A B T : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology B]
    [TopologicalSpace T] (f : A → B) (hf : Function.Injective f)
    (g : T → A) (h : Continuous (f ∘ g)) : Continuous g := by
  classical
  cases isEmpty_or_nonempty A
  · have : IsEmpty T := Function.isEmpty g
    exact continuous_of_discreteTopology
  · have hc : Continuous (Function.invFun f) := continuous_of_discreteTopology
    convert hc.comp h using 1
    funext x
    exact (Function.leftInverse_invFun hf (g x)).symm

end Topology

namespace CategoryTheory

/-- An action of a topological monoid on a finite discrete set is continuous as soon as every
orbit map is continuous. -/
public lemma action_continuous_of_orbits
    {G : Type v} [Monoid G] [TopologicalSpace G] (X : Action FintypeCat.{u} G)
    (h : ∀ x : X.V, Continuous (fun g : G ↦ (X.ρ g).hom x)) : X.IsContinuous := by
  rw [Action.isContinuous_def]
  show Continuous (fun p : G × X.V ↦ (X.ρ p.1).hom p.2)
  exact continuous_prod_of_discrete_right.mpr h

/-- An action admitting an injective morphism to a continuous action is continuous. -/
public lemma action_continuous_of_injective
    {G : Type v} [Monoid G] [TopologicalSpace G] {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) (hf : Function.Injective f.hom) (hY : Y.IsContinuous) :
    X.IsContinuous := by
  refine action_continuous_of_orbits _ fun x ↦ ?_
  apply Topology.continuous_of_injective_discrete f.hom hf
  have hc : Continuous (fun g : G ↦ (Y.ρ g).hom (f.hom x)) :=
    hY.continuous_smul.comp (continuous_id.prodMk continuous_const)
  convert hc using 1
  funext g
  exact ConcreteCategory.congr_hom (f.comm g) x

/-- Continuity of an action is inherited by limits of finite shape. -/
public instance continuous_closed_limits
    {G : Type v} [Monoid G] [TopologicalSpace G] {J : Type*} [Category J] [Finite J]
    [HasLimitsOfShape J FintypeCat.{u}]
    [PreservesLimitsOfShape J FintypeCat.incl.{u}] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  limitsOfShape_le X h := by
    obtain ⟨h⟩ := h
    let K := h.diag
    let π := h.π
    let c : Cone K := ⟨X, π⟩
    let U := forget (Action FintypeCat.{u} G)
    have : PreservesLimitsOfShape J U := by
      change PreservesLimitsOfShape J (Action.forget _ _ ⋙ FintypeCat.incl)
      infer_instance
    have hu : IsLimit (U.mapCone c) := isLimitOfPreserves U h.isLimit
    let e : X.V → (∀ j, (K.obj j).V) := fun x j ↦ (π.app j).hom x
    have he : Function.Injective e := fun x y hxy ↦
      (Types.isLimitEquivSections hu).injective (Subtype.ext hxy)
    refine action_continuous_of_orbits _ fun x ↦
      Topology.continuous_of_injective_discrete e he _ (continuous_pi fun j ↦ ?_)
    have hj : Continuous (fun g : G ↦ ((K.obj j).ρ g).hom ((π.app j).hom x)) :=
      (h.prop_diag_obj j).continuous_smul.comp (continuous_id.prodMk continuous_const)
    convert hj using 1
    funext g
    exact ConcreteCategory.congr_hom ((π.app j).comm g) x

/-- Continuity of an action is inherited by colimits. -/
public instance continuous_closed_colimits
    {G : Type v} [Monoid G] [TopologicalSpace G] {J : Type*} [Category J]
    [HasColimitsOfShape J FintypeCat.{u}]
    [PreservesColimitsOfShape J FintypeCat.incl.{u}] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  colimitsOfShape_le X h := by
    obtain ⟨h⟩ := h
    let K := h.diag
    let ι := h.ι
    let c : Cocone K := ⟨X, ι⟩
    let U := forget (Action FintypeCat.{u} G)
    have : PreservesColimitsOfShape J U := by
      change PreservesColimitsOfShape J (Action.forget _ _ ⋙ FintypeCat.incl)
      infer_instance
    have hu : IsColimit (U.mapCocone c) := isColimitOfPreserves U h.isColimit
    refine action_continuous_of_orbits _ fun x ↦ ?_
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective _ hu x
    change (ι.app j).hom y = x at hy
    subst x
    have hj : Continuous (fun g : G ↦ ((K.obj j).ρ g).hom y) :=
      (h.prop_diag_obj j).continuous_smul.comp (continuous_id.prodMk continuous_const)
    have hf : Continuous (ι.app j).hom := continuous_of_discreteTopology
    exact (hf.comp hj).congr (fun g ↦ ConcreteCategory.congr_hom ((ι.app j).comm g) y)

/-- Continuity of an action is closed under finite limits. -/
public instance {G : Type v} [Monoid G] [TopologicalSpace G] :
    ObjectProperty.IsClosedUnderFiniteLimits
    (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) where

/-- Continuity of an action is closed under finite colimits. -/
public instance {G : Type v} [Monoid G] [TopologicalSpace G] :
    ObjectProperty.IsClosedUnderFiniteColimits
    (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) where

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- The finite continuous actions of a topological group form a Galois subcategory of the
finite actions. -/
public instance : ObjectProperty.IsGaloisSubcategory
    (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) where
  isClosedUnderColimitsOfShape_discrete _ _ := by infer_instance
  isClosedUnderColimitsOfShape_singleObj _ _ _ := by infer_instance
  isClosedUnderSubobjects := ⟨fun f _ hY ↦ by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget _ _).map f))
    exact action_continuous_of_injective f
      (ConcreteCategory.injective_of_mono_of_preservesPullback f.hom) hY⟩
  preservesEpimorphisms := by infer_instance

/-- The forgetful functor from finite continuous `G`-sets to finite sets is a fibre functor. -/
public instance : PreGaloisCategory.FiberFunctor
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) := by
  change PreGaloisCategory.FiberFunctor (ObjectProperty.ι _ ⋙ Action.forget _ _)
  infer_instance

end CategoryTheory
