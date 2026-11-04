module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Restriction of a sheaf of modules to an object of the site is left exact

`SheafOfModules.overFunctor R U` restricts a sheaf of `R`-modules to the slice site over `U`.
It is the pushforward `SheafOfModules.pushforward (𝟙 (R.over U))` along `Over.forget U`, and
every such pushforward preserves finite limits.

## Main results

* `Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_restrictScalars`:
  `ModuleCat.restrictScalars f` is left exact.
* `Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward`:
  `PresheafOfModules.pushforward φ` is left exact.
* `Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_pushforward`:
  `SheafOfModules.pushforward φ` is left exact.
* `Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_overFunctor`:
  `SheafOfModules.overFunctor R U` is left exact.
* `Stacks.AlgebraicGeometry.RestrictionExact.overKernelIso`:
  `(kernel φ).over U ≅ kernel (φ.over U)`.

## Implementation notes

`preservesFiniteLimits_presheafPushforward` and `preservesFiniteLimits_pushforward` are theorems,
not instances: `φ.hom` for a sheaf-level `φ` has type
`S.val ⟶ ((F.sheafPushforwardContinuous _ J K).obj R).val`, and identifying that codomain with
`F.op ⋙ R.val` needs an unfolding that instance search does not perform.
`preservesFiniteLimits_overFunctor` is an instance, because `overFunctor R U` is a single head
symbol that search matches syntactically.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ v₂ u u₁ u₂

namespace Stacks.AlgebraicGeometry.RestrictionExact

/-! ### Change of rings on modules -/

/-- Restriction of scalars along a ring map is left exact. -/
theorem preservesFiniteLimits_restrictScalars {R : Type*} {S : Type*} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

/-! ### Pushforward of presheaves of modules -/

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- The pushforward of presheaves of modules is additive. -/
theorem additive_presheafPushforward (φ : S ⟶ F.op ⋙ R) :
    (PresheafOfModules.pushforward.{v} φ).Additive where
  map_add := by intro M N f g; ext X x; rfl

/-- The pushforward of presheaves of modules is left exact. -/
theorem preservesFiniteLimits_presheafPushforward (φ : S ⟶ F.op ⋙ R) :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{v} φ) := by
  refine ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_} hc => ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X => ?_)
  have := preservesFiniteLimits_restrictScalars.{v} (φ.app X).hom
  exact isLimitOfPreserves (ModuleCat.restrictScalars (φ.app X).hom)
    (isLimitOfPreserves (PresheafOfModules.evaluation R (op (F.obj X.unop))) hc)

end Presheaf

/-! ### Pushforward of sheaves of modules -/

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]

/-- The pushforward of sheaves of modules is additive. -/
instance additive_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (SheafOfModules.pushforward.{v} φ).Additive where
  map_add := by
    intro M N f g
    have := additive_presheafPushforward.{v} (F := F) φ.hom
    exact (SheafOfModules.forget S).map_injective
      (PresheafOfModules.pushforward.{v} (F := F) φ.hom).map_add

/-- The pushforward of sheaves of modules is left exact. -/
theorem preservesFiniteLimits_pushforward
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{v} φ) := by
  have hp := preservesFiniteLimits_presheafPushforward.{v} (F := F) φ.hom
  have h : PreservesFiniteLimits
      (SheafOfModules.pushforward.{v} φ ⋙ SheafOfModules.forget S) :=
    comp_preservesFiniteLimits (SheafOfModules.forget R)
      (PresheafOfModules.pushforward.{v} (F := F) φ.hom)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget S)

end Sheaf

/-! ### Restriction to an object of the site -/

section Over

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)

/-- Restriction of a sheaf of modules to an object of the site is additive. -/
instance additive_overFunctor : (SheafOfModules.overFunctor.{v} R U).Additive :=
  additive_pushforward.{v} _

/-- Restriction of a sheaf of modules to an object of the site is left exact. -/
instance preservesFiniteLimits_overFunctor :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{v} R U) :=
  preservesFiniteLimits_pushforward.{v} _

/-- Restriction to an object of the site commutes with kernels:
`(kernel φ).over U ≅ kernel (φ.over U)`. -/
noncomputable def overKernelIso {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    (kernel φ).over U ≅ kernel (φ.over U) :=
  PreservesKernel.iso (SheafOfModules.overFunctor.{v} R U) φ

end Over

end Stacks.AlgebraicGeometry.RestrictionExact

end
