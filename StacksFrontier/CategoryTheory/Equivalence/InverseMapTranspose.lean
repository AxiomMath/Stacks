module

public import Mathlib.CategoryTheory.Equivalence

/-!
# An equation whose left-hand side is `E.inverse` of a morphism, transposed

Let `E : C ≌ D` be an equivalence. For `b : Z ⟶ E.functor.obj Y` and
`h : E.inverse.obj Z ⟶ Y`, the equation `E.inverse.map b ≫ E.unitIso.inv.app Y = h` in `C` is
equivalent to the equation `b = E.counitIso.inv.app Z ≫ E.functor.map h` in `D`, in which neither
`E.inverse` nor the unit occurs. Morphisms of the shape `E.inverse.map b ≫ E.unitIso.inv.app Y`
are those that a construction conjugated by `E` produces.

## Main results

* `CategoryTheory.Equivalence.inverse_map_comp_unitIso_inv_eq_iff`: the transposition.
* `CategoryTheory.Equivalence.inverse_map_comp_comp_unitIso_inv_eq_iff`: the transposition with a
  prefix `E.inverse.map c` absorbed into a precomposition by `c`.
-/

@[expose] public section

namespace CategoryTheory.Equivalence

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (E : C ≌ D)

/-- **An equation out of `E.inverse.obj Z` transposed into `D`.**  For `b : Z ⟶ E.functor.obj Y`
and `h : E.inverse.obj Z ⟶ Y`, the composite `E.inverse.map b ≫ E.unitIso.inv.app Y` is `h`
exactly when `b` is `E.functor.map h` precomposed with the inverse counit at `Z`. -/
theorem inverse_map_comp_unitIso_inv_eq_iff {Z : D} {Y : C} (b : Z ⟶ E.functor.obj Y)
    (h : E.inverse.obj Z ⟶ Y) :
    E.inverse.map b ≫ E.unitIso.inv.app Y = h ↔
      b = E.counitIso.inv.app Z ≫ E.functor.map h := by
  have key : E.functor.map (E.inverse.map b ≫ E.unitIso.inv.app Y) =
      E.counitIso.hom.app Z ≫ b := by
    rw [E.functor.map_comp, ← E.counit_app_functor]
    exact E.counitIso.hom.naturality b
  constructor
  · rintro rfl
    rw [key, Iso.inv_hom_id_app_assoc]
  · rintro rfl
    exact E.functor.map_injective (by rw [key, Iso.hom_inv_id_app_assoc])

/-- **An equation out of `E.inverse.obj Z` transposed into `D`, with a prefix absorbed.** For
`c : Z ⟶ Z'`, `b : Z' ⟶ E.functor.obj Y` and `h : E.inverse.obj Z ⟶ Y`, the composite
`E.inverse.map c ≫ E.inverse.map b ≫ E.unitIso.inv.app Y` is `h` exactly when `c ≫ b` is
`E.functor.map h` precomposed with the inverse counit at `Z`. -/
theorem inverse_map_comp_comp_unitIso_inv_eq_iff {Z Z' : D} {Y : C} (c : Z ⟶ Z')
    (b : Z' ⟶ E.functor.obj Y) (h : E.inverse.obj Z ⟶ Y) :
    E.inverse.map c ≫ E.inverse.map b ≫ E.unitIso.inv.app Y = h ↔
      c ≫ b = E.counitIso.inv.app Z ≫ E.functor.map h := by
  rw [← Category.assoc, ← E.inverse.map_comp]
  exact E.inverse_map_comp_unitIso_inv_eq_iff (c ≫ b) h

end CategoryTheory.Equivalence

end
