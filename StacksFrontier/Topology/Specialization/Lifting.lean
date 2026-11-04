module

public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting specializations and generalizations along a map

## Main results

* `LiftsSpecializations`, `LiftsGeneralizations` (Stacks 0063): the Stacks project's conditions
  that specializations, resp. generalizations, lift along a map.
* `liftsSpecializations_iff_specializingMap`, `liftsGeneralizations_iff_generalizingMap`: these
  agree with Mathlib's `SpecializingMap` and `GeneralizingMap`.
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Stacks 0063.** Specializations lift along `f : X → Y` if for every `y' ⤳ y` in `Y` and every
`x' : X` with `f x' = y'` there is a specialization `x' ⤳ x` in `X` with `f x = y`. -/
@[stacks 0063, ega "II 7.2.1"]
def LiftsSpecializations (f : X → Y) : Prop :=
  ∀ ⦃x' : X⦄ ⦃y' y : Y⦄, f x' = y' → y' ⤳ y → ∃ x : X, x' ⤳ x ∧ f x = y

/-- **Stacks 0063.** Generalizations lift along `f : X → Y` if for every `y' ⤳ y` in `Y` and every
`x : X` with `f x = y` there is a generalization `x' ⤳ x` in `X` with `f x' = y'`. -/
@[stacks 0063, ega "IV 2.3.4"]
def LiftsGeneralizations (f : X → Y) : Prop :=
  ∀ ⦃x : X⦄ ⦃y' y : Y⦄, f x = y → y' ⤳ y → ∃ x' : X, x' ⤳ x ∧ f x' = y'

/-- `LiftsSpecializations` agrees with Mathlib's `SpecializingMap`. -/
theorem liftsSpecializations_iff_specializingMap (f : X → Y) :
    LiftsSpecializations f ↔ SpecializingMap f :=
  ⟨fun h _ _ hab => h rfl hab, fun h _ _ _ hfx hsp => h (hfx ▸ hsp)⟩

/-- `LiftsGeneralizations` agrees with Mathlib's `GeneralizingMap`. -/
theorem liftsGeneralizations_iff_generalizingMap (f : X → Y) :
    LiftsGeneralizations f ↔ GeneralizingMap f :=
  ⟨fun h _ _ hab => h rfl hab, fun h _ _ _ hfx hsp => h (hfx ▸ hsp)⟩
