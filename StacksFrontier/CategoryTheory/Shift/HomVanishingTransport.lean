module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Vanishing of morphisms into shifts

Two transports of the vanishing of morphisms between an object and its shifts.

## Main results

* `CategoryTheory.eq_zero_of_forall_hom_shift_neg_eq_zero`: if every morphism `K ⟶ L⟦-t⟧`
  vanishes, so does every morphism `K⟦t⟧ ⟶ L`.
* `CategoryTheory.Functor.eq_zero_of_shift_hom_eq_zero_of_faithful`: a faithful functor
  commuting with shifts reflects the vanishing of the morphisms `A⟦t⟧ ⟶ A`, read at any object
  isomorphic to the image of `A`.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]

/-- If every morphism `K ⟶ L⟦-t⟧` vanishes, so does every morphism `K⟦t⟧ ⟶ L`. -/
theorem eq_zero_of_forall_hom_shift_neg_eq_zero (t : ℤ)
    [(shiftFunctor C (-t)).PreservesZeroMorphisms] {K L : C}
    (h : ∀ g : K ⟶ (shiftFunctor C (-t)).obj L, g = 0)
    (f : (shiftFunctor C t).obj K ⟶ L) : f = 0 := by
  refine (shiftFunctor C (-t)).zero_of_map_zero f ?_
  rw [← cancel_epi ((shiftFunctorCompIsoId C t (-t) (add_neg_cancel t)).inv.app K),
    h (_ ≫ (shiftFunctor C (-t)).map f), Limits.comp_zero]

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]

/-- **A faithful functor commuting with shifts reflects the vanishing of `Hom(A⟦t⟧, A)`.** If
`ι : F A ≅ B` and every morphism `B⟦t⟧ ⟶ B` vanishes, then every morphism `A⟦t⟧ ⟶ A`
vanishes. -/
theorem Functor.eq_zero_of_shift_hom_eq_zero_of_faithful (F : C ⥤ D) [F.Faithful]
    [F.PreservesZeroMorphisms] [F.CommShift ℤ] {A : C} {B : D} (ι : F.obj A ≅ B) (t : ℤ)
    (hB : ∀ g : (shiftFunctor D t).obj B ⟶ B, g = 0) (f : (shiftFunctor C t).obj A ⟶ A) :
    f = 0 := by
  refine F.zero_of_map_zero f ?_
  calc F.map f = (F.commShiftIso t).hom.app A ≫ (shiftFunctor D t).map ι.hom ≫
        ((shiftFunctor D t).map ι.inv ≫ (F.commShiftIso t).inv.app A ≫ F.map f ≫ ι.hom) ≫
          ι.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.map_hom_inv_id_assoc,
          Iso.hom_inv_id_app_assoc]
    _ = 0 := by
        rw [hB (_ ≫ _ ≫ F.map f ≫ ι.hom), Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]

end CategoryTheory
