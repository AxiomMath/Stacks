module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Sheaf theoretically empty objects

## Main results

* `SheafTheoreticallyEmpty`: an object `U` of a site is *sheaf theoretically empty* when the
  sheafification of the map from the initial presheaf to `h_U` is an isomorphism
  (Stacks 04B5).

Tags covered: 04B5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Stacks 04B5.** An object `U` of a site is *sheaf theoretically empty* if the
sheafification of the canonical map `∅ ⟶ h_U` from the initial presheaf to the presheaf
represented by `U` is an isomorphism of sheaves. -/
@[stacks 04B5]
def SheafTheoreticallyEmpty [HasWeakSheafify J (Type v)] (U : C) : Prop :=
  IsIso ((presheafToSheaf J (Type v)).map
    (initial.to ((yoneda (C := C)).obj U)))
