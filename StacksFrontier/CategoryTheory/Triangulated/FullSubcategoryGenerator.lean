module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.CategoryTheory.Triangulated.Generators

/-!
# Generators of a triangulated subcategory, tested in the ambient category

Let `P` be a triangulated subcategory of a pretriangulated category `C` and `Q` a property of
objects of `P`. If every object `K` of `P` receiving only zero maps `E ⟶ K⟦j⟧` in `C` from the
objects `E` satisfying `Q` is zero, then `Q` is a generator of `P` in the sense of
[Stacks, Tag 09SJ](3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Generators of a triangulated subcategory may be tested in the ambient category.** Let `Q`
be a property of objects of the full subcategory `P`. If every object `K` of `C` satisfying `P`
and receiving only zero maps `E ⟶ K⟦j⟧` from the objects `E` satisfying `Q` is zero, then `Q` is
a weak generator of `P`. -/
theorem isWeakTriangulatedGenerator_of_forall_hom_eq_zero (P : ObjectProperty C)
    [P.IsTriangulated] (Q : ObjectProperty P.FullSubcategory)
    (h : ∀ K : C, P K → (∀ E, Q E → ∀ (j : ℤ) (g : E.obj ⟶ K⟦j⟧), g = 0) → IsZero K) :
    Q.IsWeakTriangulatedGenerator := by
  rw [isWeakTriangulatedGenerator_iff]
  intro K hK
  by_contra! hc
  refine hK (IsZero.of_full_of_faithful_of_isZero P.ι K
    (h K.obj K.property fun E hE j g => ?_))
  let e := (P.ι.commShiftIso j).app K
  have h1 : g ≫ e.inv = 0 := by
    rw [← P.fullyFaithfulι.map_preimage (X := E) (Y := K⟦j⟧) (g ≫ e.inv),
      hc E hE j (P.fullyFaithfulι.preimage (g ≫ e.inv)), Functor.map_zero]
  exact ((Iso.comp_inv_eq e).1 h1).trans zero_comp

/-- **A generator of a triangulated subcategory may be tested in the ambient category.** If every
object `K` of `C` satisfying `P` and receiving only zero maps `E ⟶ K⟦j⟧` is zero, then `E` is a
weak generator of the full subcategory `P`. -/
theorem isWeakTriangulatedGenerator_singleton_of_forall_hom_eq_zero (P : ObjectProperty C)
    [P.IsTriangulated] (E : P.FullSubcategory)
    (h : ∀ K : C, P K → (∀ (j : ℤ) (g : E.obj ⟶ K⟦j⟧), g = 0) → IsZero K) :
    (ObjectProperty.singleton E).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_of_forall_hom_eq_zero P _ fun K hK hvan =>
    h K hK (hvan E ((ObjectProperty.singleton_iff _ _).2 rfl))

end CategoryTheory.ObjectProperty
