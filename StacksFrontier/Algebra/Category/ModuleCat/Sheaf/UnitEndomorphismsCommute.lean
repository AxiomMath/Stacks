module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Endomorphisms of the unit module of a sheaf of commutative rings commute

For a sheaf of rings `R` whose rings of sections are commutative, an endomorphism `φ` of the
unit module `R` is multiplication by `φ(1)` on every ring of sections, so any two endomorphisms
commute.

## Main results

* `SheafOfModules.unit_endomorphisms_commute` — `g ≫ h = h ≫ g` for `g h : unit R ⟶ unit R`.
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- An endomorphism of the unit module is multiplication by its value at `1`. -/
theorem unit_hom_app_eq_smul (φ : unit R ⟶ unit R) (U : Cᵒᵖ) (y : (unit R).val.obj U) :
    φ.val.app U y = (show R.obj.obj U from y) • φ.val.app U (show R.obj.obj U from 1) := by
  have h := (φ.val.app U).hom.map_smul (show R.obj.obj U from y) (show R.obj.obj U from 1)
  have h1 : (show R.obj.obj U from y) • (show (unit R).val.obj U from (1 : R.obj.obj U)) = y :=
    mul_one (show R.obj.obj U from y)
  rw [h1] at h
  exact h

/-- **Endomorphisms of the unit module commute** when the rings of sections are commutative. -/
theorem unit_endomorphisms_commute (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (g h : unit R ⟶ unit R) : g ≫ h = h ≫ g := by
  ext U
  exact (unit_hom_app_eq_smul h U (g.val.app U (1 : R.obj.obj U))).trans
    ((hR U _ _).trans (unit_hom_app_eq_smul g U (h.val.app U (1 : R.obj.obj U))).symm)

end SheafOfModules
