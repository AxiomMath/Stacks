module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restriction of scalars along equal morphisms of sheaves of rings

For equal morphisms `α β : R ⟶ R'` of sheaves of rings, this file gives the natural isomorphism
between `SheafOfModules.restrictScalars α` and `SheafOfModules.restrictScalars β` whose components
are the identity on sections. It is the sheaf-of-modules analogue of
`ModuleCat.restrictScalarsCongr`.

## Main definitions

* `SheafOfModules.restrictScalarsCongr`: the identification of the two restrictions of scalars.

## Main results

* `SheafOfModules.restrictScalarsCongr_hom_app_val_app` and
  `SheafOfModules.restrictScalarsCongr_inv_app_val_app`: its components are the identity on
  sections.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v' u u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}}

/-- Restriction of scalars along equal morphisms of sheaves of rings, as a natural isomorphism
whose components are the identity on sections. -/
def restrictScalarsCongr {α β : R ⟶ R'} (e : α = β) :
    restrictScalars.{v} α ≅ restrictScalars.{v} β :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl)) fun _ ↦ by subst e; rfl

/-- The component of `restrictScalarsCongr e` at `M` is the identity on sections. -/
@[simp]
lemma restrictScalarsCongr_hom_app_val_app {α β : R ⟶ R'} (e : α = β)
    (M : SheafOfModules.{v} R') (U : Cᵒᵖ) (x : ((restrictScalars.{v} α).obj M).val.obj U) :
    ((restrictScalarsCongr.{v} e).hom.app M).val.app U x = x := rfl

/-- The inverse component of `restrictScalarsCongr e` at `M` is the identity on sections. -/
@[simp]
lemma restrictScalarsCongr_inv_app_val_app {α β : R ⟶ R'} (e : α = β)
    (M : SheafOfModules.{v} R') (U : Cᵒᵖ) (x : ((restrictScalars.{v} β).obj M).val.obj U) :
    ((restrictScalarsCongr.{v} e).inv.app M).val.app U x = x := rfl

end SheafOfModules

end
