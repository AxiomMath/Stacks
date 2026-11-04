module

public import Mathlib.CategoryTheory.Types.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-! # The presheaf of maps out of a functor to sets

## Main results

* `pushforwardPresheaf04EI`: for a functor `u : C ⥤ Type` and a type `E`, the presheaf
  `u^p E : U ↦ (u U → E)` with restriction maps given by precomposition with `u` (Stacks 04EI).
* `pushforwardPresheaf_obj`, `pushforwardPresheaf_map`: its values on objects and morphisms.

Tags covered: 04EI.
-/

@[expose] public section

open CategoryTheory

universe u v

/-- **Stacks 04EI.** The presheaf `u^p E` attached to a functor `u : C ⥤ Type` and a type `E`:
it sends an object `U` to the type of functions `u U → E`, and a morphism `f : V ⟶ U` to
precomposition with `u f`. -/
@[stacks 04EI, sga "4 I 1.3" "special case"]
def pushforwardPresheaf04EI {C : Type u} [Category.{v} C] (u : Functor C (Type v)) (E : Type v) :
    Functor Cᵒᵖ (Type v) where
  obj U := u.obj U.unop → E
  map f := ↾(fun φ x => φ (u.map f.unop x))
  map_id U := by
    ext φ x
    simp [TypeCat.ofHom]
  map_comp f g := by
    ext φ x
    simp [TypeCat.ofHom]

attribute [implicit_reducible] pushforwardPresheaf04EI

/-- The sections of `u^p E` over `U` are the functions `u U → E`. -/
@[sga "4 I 1.3" "special case"]
theorem pushforwardPresheaf_obj {C : Type u} [Category.{v} C]
    (u : Functor C (Type v)) (E : Type v) (U : Cᵒᵖ) :
    (pushforwardPresheaf04EI u E).obj U = (u.obj U.unop → E) := rfl

/-- The restriction map of `u^p E` along `f.op`, for `f : U ⟶ V`, is precomposition with `u f`:
it sends `φ : u V → E` to `φ ∘ u f`. -/
@[sga "4 I 1.3" "(f), special case"]
theorem pushforwardPresheaf_map {C : Type u} [Category.{v} C]
    (u : Functor C (Type v)) (E : Type v) {U V : C} (f : U ⟶ V)
    (φ : u.obj V → E) :
    (pushforwardPresheaf04EI u E).map f.op φ = φ ∘ u.map f :=
  rfl
