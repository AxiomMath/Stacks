module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Cancellations and section readings shared by the comorphism-through-a-thickening files

The files of `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/` which compare the two readings
of [Stacks Project, Tag 03G8] work with composites of very large morphisms of sheaves of rings on
the small étale site.  As the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` record, `rw` and
`simp only [Category.assoc]` are not reliable at those terms, so every rearrangement is stated
over an abstract category with each morphism a variable and discharged by `exact`.

This module holds the rearrangements and section readings that **more than one** of those files
needs, so that each exists exactly once.

## Main results

* `AlgebraicGeometry.Space.comp_cancel_right`: cancelling the right factor of a composite
  against a right inverse.
* `AlgebraicGeometry.Space.cancel_right_of_comp_id`: a morphism with a right inverse is a
  monomorphism, in the form the cancellations use.
* `AlgebraicGeometry.Space.setSheafHom_congr_app_apply`: an equation between morphisms of
  sheaves of sets, read on sections.
* `AlgebraicGeometry.Space.ringSheafHom_comp_app_apply`: the value of a composite of morphisms
  of sheaves of rings on a section.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public section

open CategoryTheory

universe uu vv u

namespace AlgebraicGeometry.Space

/-- Cancelling the right factor of a composite against a right inverse. -/
theorem comp_cancel_right {Cc : Type*} [Category Cc] {A Bb D : Cc} (a : A ⟶ Bb)
    (k : Bb ⟶ D) (k' : D ⟶ Bb) (hk : k ≫ k' = 𝟙 Bb) : (a ≫ k) ≫ k' = a := by
  rw [Category.assoc, hk, Category.comp_id]

/-- A morphism with a right inverse is a monomorphism, in the form the cancellation uses. -/
theorem cancel_right_of_comp_id {Cc : Type*} [Category Cc] {A Bb D : Cc}
    (a b : A ⟶ Bb) (k : Bb ⟶ D) (k' : D ⟶ Bb) (hk : k ≫ k' = 𝟙 Bb)
    (hab : a ≫ k = b ≫ k) : a = b := by
  rw [← Category.comp_id a, ← hk, ← Category.assoc, hab, Category.assoc, hk, Category.comp_id]

/-- An equation between morphisms of sheaves of sets, read on sections. -/
theorem setSheafHom_congr_app_apply {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {P Q : Sheaf Jc (Type u)} {a b : P ⟶ Q} (h : a = b)
    (W : Ccᵒᵖ) (x : P.obj.obj W) : a.hom.app W x = b.hom.app W x := by rw [h]

/-- The value of a composite of morphisms of sheaves of rings on a section.  Stated over an
abstract site, so that the kernel checks the `rfl` once and in a statement whose terms are
variables; instantiated at the geometric terms of the small étale site it is a deterministic
timeout. -/
theorem ringSheafHom_comp_app_apply {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {A Bb Cd : Sheaf Jc RingCat.{u}} (a : A ⟶ Bb) (b : Bb ⟶ Cd)
    (V : Ccᵒᵖ) (z : A.obj.obj V) : (a ≫ b).hom.app V z = b.hom.app V (a.hom.app V z) := rfl

end AlgebraicGeometry.Space

end
