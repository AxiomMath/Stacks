module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.Homology.TensorComplex.ExactFunctor

/-!
# `TrightCochain` at the tensor unit

Tensoring a cochain complex on the right with the tensor unit is the identity functor.

## Main results

* `trightCochainTensorUnitIso`: `TrightCochain` at the tensor unit of `CochainComplex C ℤ` is
  isomorphic to the identity functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- `TrightCochain` at the tensor unit of `CochainComplex C ℤ` is the identity functor. -/
public noncomputable def trightCochainTensorUnitIso (C : Type*) [Category* C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasZeroObject C] [HasColimits C] :
    TrightCochain (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)) ≅
      𝟭 (CochainComplex C ℤ) := by
  refine (NatIso.ofComponents (fun K => (HomologicalComplex.rightUnitor K).symm) ?_).symm
  intro X Y f
  ext n
  change f.f n ≫ (HomologicalComplex.rightUnitor' Y).inv n =
    (HomologicalComplex.rightUnitor' X).inv n ≫
      (HomologicalComplex.tensorHom f (𝟙 _)).f n
  simp only [HomologicalComplex.rightUnitor'_inv, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, HomologicalComplex.id_f,
    whiskerLeft_id]
  rw [whisker_exchange_assoc, rightUnitor_inv_naturality_assoc]
  simp

end
