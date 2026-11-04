module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Vanishing of morphisms into shifts, transported along a functor

A functor commuting with shifts which is surjective on the morphisms `A ⟶ B⟦i⟧` carries the
vanishing of these morphisms to all objects isomorphic to the images of `A` and `B`.

## Main results

* `CategoryTheory.Functor.eq_zero_of_hom_shift_eq_zero_of_surjective`: if every morphism
  `A ⟶ B⟦i⟧` vanishes and `F` is surjective on them, every morphism `A' ⟶ B'⟦i⟧` vanishes,
  for `A' ≅ F A` and `B' ≅ F B`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasShift C ℤ] [HasShift D ℤ]

/-- **Vanishing of morphisms into a shift, transported along a functor surjective on them.**
Let `F` commute with shifts and be surjective on the morphisms `A ⟶ B⟦i⟧`. If all these
vanish, so does every morphism `A' ⟶ B'⟦i⟧`, for `A' ≅ F A` and `B' ≅ F B`. -/
theorem Functor.eq_zero_of_hom_shift_eq_zero_of_surjective (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.CommShift ℤ] {A B : C} {A' B' : D} (eA : F.obj A ≅ A')
    (eB : F.obj B ≅ B') (i : ℤ)
    (hF : Function.Surjective (F.map : (A ⟶ (shiftFunctor C i).obj B) → _))
    (hA : ∀ g : A ⟶ (shiftFunctor C i).obj B, g = 0) (g : A' ⟶ (shiftFunctor D i).obj B') :
    g = 0 := by
  obtain ⟨h, hh⟩ := hF (eA.hom ≫ g ≫ (shiftFunctor D i).map eB.inv ≫
    (F.commShiftIso i).inv.app B)
  calc g = eA.inv ≫ (eA.hom ≫ g ≫ (shiftFunctor D i).map eB.inv ≫
        (F.commShiftIso i).inv.app B) ≫ (F.commShiftIso i).hom.app B ≫
        (shiftFunctor D i).map eB.hom := by
          simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc,
            ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
    _ = 0 := by rw [← hh, hA h, F.map_zero, zero_comp, comp_zero]

end CategoryTheory
