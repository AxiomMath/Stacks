module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleAcyclic

/-!
# Transporting the unit at objects in degree zero along an equality of functors

Let `w, w' : A ⥤ B` be additive functors with `w' = w`, and let `α` be the unit of a right
derived functor `Rw` of `w'`. Precomposed with `eqToHom` of the induced equality
`w ⋙ Qh = w' ⋙ Qh` on homotopy categories, `α` is a unit for `w`. This file compares the two
transformations `w(-)[0] ⟶ Rw(-[0])` and `w'(-)[0] ⟶ Rw(-[0])` that
`Stacks.DerivedFunctor.singleUnit` attaches to these units: they differ by the
identification `w ⋙ [0] ≅ w' ⋙ [0]`.

Both statements are equalities of natural transformations. Their components are recovered by
`NatTrans.congr_app`. Comparing the two transformations componentwise directly, with two
spellings of the same functor, is much more expensive for the kernel.

## Main results

* `Stacks.DerivedFunctor.singleUnit_eqToHom_comp`: the unit for `w` through the `eqToHom`
  transport is the identification followed by the unit for `w'`.
* `Stacks.DerivedFunctor.singleUnit_eq_comp_eqToHom`: the same, solved for the unit for `w'`.
-/

@[expose] public noncomputable section

open CategoryTheory DerivedCategory

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- **The unit at objects in degree zero, transported along `w' = w`**: for a unit `α` of `Rw`
as a right derived functor of `w'`, `singleUnit` of `w` at `eqToHom _ ≫ α` is the
identification `w ⋙ [0] ≅ w' ⋙ [0]` followed by `singleUnit` of `w'` at `α`. -/
theorem singleUnit_eqToHom_comp (w w' : A ⥤ B) [hw₁ : w.Additive] [hw₂ : w'.Additive]
    (hw : w' = w) (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (h : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh =
      w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (α : w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw) :
    singleUnit w Rw (eqToHom h ≫ α) =
      (Functor.isoWhiskerRight (eqToIso hw) (DerivedCategory.singleFunctor B 0)).inv ≫
        singleUnit w' Rw α := by
  subst hw
  simp

/-- `Stacks.DerivedFunctor.singleUnit_eqToHom_comp` solved for the unit of `w'`:
`singleUnit` of `w'` at `α` is the identification `w' ⋙ [0] ≅ w ⋙ [0]` followed by
`singleUnit` of `w` at `eqToHom _ ≫ α`. -/
theorem singleUnit_eq_comp_eqToHom (w w' : A ⥤ B) [hw₁ : w.Additive] [hw₂ : w'.Additive]
    (hw : w' = w) (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (h : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh =
      w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (α : w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw) :
    singleUnit w' Rw α =
      (Functor.isoWhiskerRight (eqToIso hw) (DerivedCategory.singleFunctor B 0)).hom ≫
        singleUnit w Rw (eqToHom h ≫ α) := by
  subst hw
  simp

end Stacks.DerivedFunctor
