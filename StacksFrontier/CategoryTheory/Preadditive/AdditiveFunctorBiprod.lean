module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# An additive functor that kills one summand of a biproduct

Let `F : C ⥤ D` be an additive functor between preadditive categories and let `A ⊞ B` be a
binary biproduct in `C`. If `F.obj B` is a zero object, then `F` sends the projection onto and the
inclusion of `A` to isomorphisms, and symmetrically when `F.obj A` is a zero object.

## Main results

* `CategoryTheory.map_biprod_fst_comp_map_biprod_inl`: if `F.obj B` is zero, then
  `F.map biprod.fst ≫ F.map biprod.inl` is the identity of `F.obj (A ⊞ B)`.
* `CategoryTheory.map_biprod_snd_comp_map_biprod_inr`: if `F.obj A` is zero, then
  `F.map biprod.snd ≫ F.map biprod.inr` is the identity of `F.obj (A ⊞ B)`.
* `CategoryTheory.isIso_map_biprod_fst_of_isZero` and
  `CategoryTheory.isIso_map_biprod_inl_of_isZero`: the projection to and the inclusion of the
  first summand become isomorphisms when the second summand is sent to zero.
* `CategoryTheory.isIso_map_biprod_snd_of_isZero`: the projection to the second summand becomes
  an isomorphism when the first summand is sent to zero.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {A B : C} [HasBinaryBiproduct A B]

/-- If an additive functor sends the second summand of a biproduct to a zero object, then the
image of the projection to the first summand followed by the image of the inclusion of the first
summand is the identity. -/
public theorem map_biprod_fst_comp_map_biprod_inl (hB : IsZero (F.obj B)) :
    F.map (biprod.fst : A ⊞ B ⟶ A) ≫ F.map (biprod.inl : A ⟶ A ⊞ B) =
      𝟙 (F.obj (A ⊞ B)) := by
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hB.eq_of_tgt (F.map biprod.snd) 0, zero_comp, add_zero]

/-- If an additive functor sends the first summand of a biproduct to a zero object, then the image
of the projection to the second summand followed by the image of the inclusion of the second
summand is the identity. -/
public theorem map_biprod_snd_comp_map_biprod_inr (hA : IsZero (F.obj A)) :
    F.map (biprod.snd : A ⊞ B ⟶ B) ≫ F.map (biprod.inr : B ⟶ A ⊞ B) =
      𝟙 (F.obj (A ⊞ B)) := by
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hA.eq_of_tgt (F.map biprod.fst) 0, zero_comp, zero_add]

/-- An additive functor which kills the second summand of a biproduct sends the inclusion of the
first summand to an isomorphism. -/
public theorem isIso_map_biprod_inl_of_isZero (hB : IsZero (F.obj B)) :
    IsIso (F.map (biprod.inl : A ⟶ A ⊞ B)) :=
  ⟨F.map biprod.fst, by simp [← F.map_comp], map_biprod_fst_comp_map_biprod_inl F hB⟩

/-- An additive functor which kills the second summand of a biproduct sends the projection to
the first summand to an isomorphism. -/
public theorem isIso_map_biprod_fst_of_isZero (hB : IsZero (F.obj B)) :
    IsIso (F.map (biprod.fst : A ⊞ B ⟶ A)) :=
  ⟨F.map biprod.inl, map_biprod_fst_comp_map_biprod_inl F hB, by simp [← F.map_comp]⟩

/-- An additive functor which kills the first summand of a biproduct sends the projection to the
second summand to an isomorphism. -/
public theorem isIso_map_biprod_snd_of_isZero (hA : IsZero (F.obj A)) :
    IsIso (F.map (biprod.snd : A ⊞ B ⟶ B)) :=
  ⟨F.map biprod.inr, map_biprod_snd_comp_map_biprod_inr F hA, by simp [← F.map_comp]⟩

end CategoryTheory

end
