module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# An additive functor carries a matrix of morphisms to the matrix of its values

Let `F : C ⥤ D` be an additive functor between preadditive categories with finite biproducts.
`F` carries a finite biproduct to a finite biproduct, by
`CategoryTheory.Functor.mapBiproduct`, and the content of this file is that the comparison
isomorphism turns the morphism of biproducts given by a matrix `m` into the morphism given by the
matrix of the values of `F`:

`(F.mapBiproduct f).inv ≫ F(matrix m) ≫ (F.mapBiproduct g).hom = matrix (fun j k ↦ F(m j k))`.

Two companion computations are recorded with it: a biproduct whose summands `F` annihilates is
annihilated by `F`, and composing a matrix with a diagonal morphism multiplies the matrix by the
diagonal entries on the corresponding side. Together they are what it takes to read a complex of
biproducts — a Koszul complex, say — through an additive functor as the complex of biproducts of
the images, with the matrix of the differential unchanged.

## Main results

* `CategoryTheory.Functor.isZero_obj_biproduct`: **an additive functor annihilating every summand
  annihilates the biproduct.**
* `CategoryTheory.Functor.mapBiproduct_inv_map_matrix`: **an additive functor carries a matrix to
  the matrix of its values.**
* `CategoryTheory.Limits.biproduct.matrix_comp_map` and
  `CategoryTheory.Limits.biproduct.map_comp_matrix`: composition of a matrix with a diagonal
  morphism.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] [HasFiniteBiproducts C]
  {J K : Type} [Finite J] [Finite K] {f : J → C} {g : K → C}

/-- **Composing a matrix with a diagonal morphism on the right** multiplies each column of the
matrix by the corresponding diagonal entry. -/
theorem biproduct.matrix_comp_map {g' : K → C} (m : ∀ j k, f j ⟶ g k) (h : ∀ k, g k ⟶ g' k) :
    biproduct.matrix m ≫ biproduct.map h = biproduct.matrix fun j k => m j k ≫ h k := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  simp

/-- **Composing a matrix with a diagonal morphism on the left** multiplies each row of the matrix
by the corresponding diagonal entry. -/
theorem biproduct.map_comp_matrix {f' : J → C} (h : ∀ j, f j ⟶ f' j) (m : ∀ j k, f' j ⟶ g k) :
    biproduct.map h ≫ biproduct.matrix m = biproduct.matrix fun j k => h j ≫ m j k := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  simp

end Limits

namespace Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Additive]

omit [HasFiniteBiproducts D] in
/-- **An additive functor which annihilates every summand of a finite biproduct annihilates the
biproduct.** -/
theorem isZero_obj_biproduct {J : Type} [Finite J] (f : J → C)
    (h : ∀ j, IsZero (F.obj (f j))) : IsZero (F.obj (⨁ f)) := by
  refine IsZero.of_iso ?_ (F.mapBiproduct f)
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  exact (h j).eq_of_src _ _

/-- **An additive functor carries the morphism of biproducts given by a matrix to the morphism
given by the matrix of its values.** -/
theorem mapBiproduct_inv_map_matrix {J K : Type} [Finite J] [Finite K] {f : J → C} {g : K → C}
    (m : ∀ j k, f j ⟶ g k) :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.matrix m) ≫ (F.mapBiproduct g).hom =
      biproduct.matrix fun j k => F.map (m j k) := by
  have h : (F.mapBiproduct f).inv ≫ F.map (biproduct.matrix m) ≫ (F.mapBiproduct g).hom =
      (biproduct.desc fun j => F.map (biproduct.lift fun k => m j k)) ≫
        (F.mapBiproduct g).hom := by
    rw [← Category.assoc, ← biproduct.mapBiproduct_inv_map_desc]
    rfl
  rw [h]
  refine biproduct.hom_ext' _ _ fun j => ?_
  rw [biproduct.ι_desc_assoc, biproduct.map_lift_mapBiprod, biproduct.ι_matrix]

end Functor

end CategoryTheory

end
