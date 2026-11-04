module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Quotients of subobjects along equal inclusions

For subobjects `W ≤ N` and `W' ≤ N'` of an object, equalities `W = W'` and `N = N'` identify the
quotients `N / W` and `N' / W'`.

The identification is needed wherever a quotient of subobjects is computed twice through
different but equal descriptions, which happens throughout the construction of the spectral
sequence of a filtered complex and of a filtered differential object. It asks only for zero
morphisms and cokernels, so it lives here, below every development that uses it.

## Main definitions

* `CategoryTheory.Subobject.cokernelOfLEIsoOfEq`: the identification `N / W ≅ N' / W'`.

## Main results

* `CategoryTheory.Subobject.π_cokernelOfLEIsoOfEq_hom`: the identification is induced by the
  inclusion `N ⟶ N'`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Subobject

open Limits

/-- The isomorphism `W / N ≅ W' / N'` induced by equalities `W = W'`, `N = N'` of subobjects. -/
noncomputable def cokernelOfLEIsoOfEq {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    [HasCokernels A] {Y : A}
    {W N W' N' : Subobject Y} (h : W ≤ N) (h' : W' ≤ N') (hW : W = W') (hN : N = N') :
    cokernel (Subobject.ofLE W N h) ≅ cokernel (Subobject.ofLE W' N' h') where
  hom := cokernel.desc _ (Subobject.ofLE N N' hN.le ≫ cokernel.π _) (by
    rw [Subobject.ofLE_comp_ofLE_assoc, ← Subobject.ofLE_comp_ofLE _ W' _ hW.le h',
      Category.assoc, cokernel.condition, comp_zero])
  inv := cokernel.desc _ (Subobject.ofLE N' N hN.ge ≫ cokernel.π _) (by
    rw [Subobject.ofLE_comp_ofLE_assoc, ← Subobject.ofLE_comp_ofLE _ W _ hW.ge h,
      Category.assoc, cokernel.condition, comp_zero])
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp
  inv_hom_id := by
    refine coequalizer.hom_ext ?_
    simp

/-- The isomorphism `cokernelOfLEIsoOfEq` is induced by the inclusion `N ⟶ N'`. -/
@[reassoc (attr := simp)]
lemma π_cokernelOfLEIsoOfEq_hom {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    [HasCokernels A] {Y : A}
    {W N W' N' : Subobject Y} (h : W ≤ N) (h' : W' ≤ N') (hW : W = W') (hN : N = N') :
    cokernel.π _ ≫ (cokernelOfLEIsoOfEq h h' hW hN).hom =
      Subobject.ofLE N N' hN.le ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

end CategoryTheory.Subobject

end
