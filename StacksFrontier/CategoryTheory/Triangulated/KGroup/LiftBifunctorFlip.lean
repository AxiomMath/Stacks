module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic

/-!
# The flip of a restricted bifunctor and its shift commutation

For a bifunctor `F : C ⥤ C ⥤ C` on a pretriangulated category and a triangulated full
subcategory `P` closed under `F`, this file describes the components of the isomorphism
`liftBifunctorFlipObjCompιIso` and shows that the restricted bifunctor `liftBifunctor P F hF`
is compatible with the shift in its left variable naturally in its right variable.

## Main results

* `liftBifunctor_flip_map_commShift`: for a morphism `g : Z ⟶ Z'` in the subcategory, the natural
  transformation `(liftBifunctor P F hF).flip.map g` commutes with the shift, provided each
  `F.flip.map` does.
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.Pretriangulated.K0

universe v u v' u'

namespace TensorStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (T : TensorStructure C)

end TensorStructure

namespace TensorAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {T : TensorStructure C}
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (A : TensorAction T D)

end TensorAction

section Monoidal

open CategoryTheory.MonoidalCategory

end Monoidal

section Subcategory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The components of the forward map of `liftBifunctorFlipObjCompιIso P F hF Z` are
identities. -/
lemma liftBifunctorFlipObjCompιIso_hom_app (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z)) (Z Y : P.FullSubcategory) :
    (liftBifunctorFlipObjCompιIso P F hF Z).hom.app Y = 𝟙 _ :=
  rfl

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The components of the inverse map of `liftBifunctorFlipObjCompιIso P F hF Z` are
identities. -/
@[simp]
lemma liftBifunctorFlipObjCompιIso_inv_app (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z)) (Z Y : P.FullSubcategory) :
    (liftBifunctorFlipObjCompιIso P F hF Z).inv.app Y = 𝟙 _ :=
  rfl

variable (P : ObjectProperty C) [P.IsTriangulated] (F : C ⥤ C ⥤ C)
  (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z))

/-- If each `F.flip.map g` commutes with the shift, then so does
`(liftBifunctor P F hF).flip.map g` for every morphism `g` of the full subcategory, with the shift
structures `liftBifunctorCommShiftLeft`. -/
theorem liftBifunctor_flip_map_commShift (csL : ∀ Z : C, (F.flip.obj Z).CommShift ℤ)
    (hL : ∀ {Z Z' : C} (g : Z ⟶ Z'), letI := csL Z; letI := csL Z';
      NatTrans.CommShift (F.flip.map g) ℤ)
    {Z Z' : P.FullSubcategory} (g : Z ⟶ Z') :
    letI := liftBifunctorCommShiftLeft P F hF csL Z
    letI := liftBifunctorCommShiftLeft P F hF csL Z'
    NatTrans.CommShift ((liftBifunctor P F hF).flip.map g) ℤ := by
  let := liftBifunctorCommShiftLeft P F hF csL Z
  let := liftBifunctorCommShiftLeft P F hF csL Z'
  let := csL Z.obj
  let := csL Z'.obj
  have := hL g.hom
  have := Functor.CommShift.ofComp_compatibility (liftBifunctorFlipObjCompιIso P F hF Z) ℤ
  have := Functor.CommShift.ofComp_compatibility (liftBifunctorFlipObjCompιIso P F hF Z') ℤ
  refine NatTrans.commShift_of_whiskerRight _ P.ι ?_
  refine NatTrans.commShift_of_eq_conj (liftBifunctorFlipObjCompιIso P F hF Z)
    (liftBifunctorFlipObjCompιIso P F hF Z') (Functor.whiskerLeft P.ι (F.flip.map g.hom)) ?_
  ext Y
  exact ((Category.comp_id (obj := C) _).symm.trans (Category.id_comp (obj := C) _).symm)

end Subcategory

end CategoryTheory.Pretriangulated.K0

end

end
