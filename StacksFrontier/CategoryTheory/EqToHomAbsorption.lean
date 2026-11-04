module

public import Mathlib.CategoryTheory.EqToHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Absorbing an `eqToHom` out of a composite

An `eqToHom h` built from `h : X = X` is the identity (`CategoryTheory.eqToHom_refl`), so it
contributes nothing to a composite. Mathlib states that fact for the morphism alone; this file
states the two composite forms, which are what an `exact` or a `congrArg` needs. A trailing pair
`eqToHom h ≫ eqToHom h.symm` is absorbed for the same reason, and that form is collected here
too.

The point of having them is that they apply where `Category.id_comp` and `Category.comp_id` do
not. A morphism `eqToHom h : X ⟶ Y` arising from an identification of objects that holds *by
definition* — for instance the identification of the shift of a quotient category with the
quotient of a shift, which is true by `rfl` but is not an unfolding any tactic performs while
matching — composes with a morphism out of `Y`, and the resulting
`CategoryTheory.CategoryStruct.comp` records `X` and `Y` as two different expressions. The
pattern `𝟙 ?X ≫ ?f` of `Category.id_comp` requires those two to be syntactically equal, so
`rw` and `simp` cannot fire. The lemmas below are instead stated with a single object, and are
applied in *term* position, where the elaborator checks `X` against `Y` by full definitional
unfolding and succeeds.

## Main results

* `CategoryTheory.eqToHom_comp_of_refl` and `CategoryTheory.comp_eqToHom_of_refl`: an
  `eqToHom` on a reflexive equation is absorbed on the left, resp. on the right, of a composite.
* `CategoryTheory.comp_eqToHom_comp_eqToHom_symm`: an `eqToHom` followed by the `eqToHom` of the
  symmetric equation is absorbed off the end of a composite.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- An `eqToHom` built from an equation of an object with itself is absorbed on the left of a
composite. Applied in term position this also covers an `eqToHom` between two objects that are
only definitionally equal, which is what `Category.id_comp` cannot match. -/
theorem eqToHom_comp_of_refl {X Z : C} (h : X = X) (g : X ⟶ Z) : eqToHom h ≫ g = g := by
  rw [eqToHom_refl, Category.id_comp]

/-- An `eqToHom` built from an equation of an object with itself is absorbed on the right of a
composite. Applied in term position this also covers an `eqToHom` between two objects that are
only definitionally equal, which is what `Category.comp_id` cannot match. -/
theorem comp_eqToHom_of_refl {W X : C} (h : X = X) (f : W ⟶ X) : f ≫ eqToHom h = f := by
  rw [eqToHom_refl, Category.comp_id]

/-- Transporting along an equation of objects and then back along its symmetric form leaves a
morphism unchanged. The two `eqToHom`s are a mutually inverse pair, so this is the composite
counterpart of `CategoryTheory.eqToHom_trans_symm`. -/
theorem comp_eqToHom_comp_eqToHom_symm {X Y Z : C} (f : X ⟶ Y) (h : Y = Z) :
    (f ≫ eqToHom h) ≫ eqToHom h.symm = f := by
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end CategoryTheory
