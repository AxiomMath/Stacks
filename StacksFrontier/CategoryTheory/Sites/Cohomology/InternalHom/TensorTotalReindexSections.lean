module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalShiftSections

/-!
# The total tensor complex and the sign-free reindexing of its second factor

Let `X` be a ringed site, let `A`, `Z` be complexes of `O`-modules and let `k` be an integer.
This file identifies

`Tot(A ⊗_O reindexBy Z k) ≅ reindexBy (Tot(A ⊗_O Z)) k`

and computes the identification on the local pure tensors, where it has **no sign**: the pure
tensor of a degree-`t` section of `A` with a degree-`r` section of `reindexBy Z k` — that is, a
degree-`k + r` section of `Z` — goes to the pure tensor of the same two sections, read in the
degree `k + (t + r)`.

That the comparison is sign-free is the point of the sign-free reindexing
`CochainComplex.reindexBy`, and it is not automatic: the comparison is assembled out of
`Mathlib`'s comparison with the *shift*, which does carry a sign, applied in the second variable
and then undone on the total complex. Three signs appear in the course of the proof and they
cancel exactly, by `CochainComplex.negOnePow_shift_summand_cancel`. This is the only place where
they meet, which is why the reindexing was introduced instead of working with the shift
throughout.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalMapIso₂`: an isomorphism of the second tensor factor
  induces an isomorphism of total tensor complexes.
* `AlgebraicGeometry.RingedSite.tensorTotalReindexIso₂`: the comparison above.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalReindexIso₂_tensorTotalSection`: the comparison on a
  local pure tensor, with no sign.

## Implementation notes

The three signs are, in the order in which they are paid: `(-1)^{kr}` from
`CochainComplex.reindexByIsoShift` at `Z` in degree `r`, which is how the reindexed second
factor is turned into a shifted one; `(-1)^{tk}` from
`AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂_tensorTotalSection`, which is `Mathlib`'s
summand sign; and `(-1)^{k(t + r)}` from `CochainComplex.reindexByIsoShift` at `Tot(A ⊗_O Z)` in
degree `t + r`, which is how the shifted total complex is turned back into a reindexed one. The
first two multiply to the third, and the third appears twice.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 06YS)](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

variable (X : RingedSite.{u, u, u})

/-- The value on a local section of a morphism of sheaves of modules scaled by a unit of `ℤ`.
Only the sign `-1` occurs, and only through `Int.negOnePow`, which is valued in `ℤˣ`. -/
private lemma units_smul_val_app_apply
    {P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (u : ℤˣ)
    (φ : P ⟶ Q) (W : X.Cᵒᵖ) (x : P.val.obj W) :
    ((u • φ).val.app W) x = u • ((φ.val.app W) x) := by
  rw [Units.smul_def, show ((u : ℤ) • φ).val = (u : ℤ) • φ.val from rfl,
    PresheafOfModules.zsmul_app]
  rfl

/-- **An isomorphism of the second tensor factor induces an isomorphism of total tensor
complexes.** The inverse is the total tensor-product morphism of the inverse, by the
functoriality `AlgebraicGeometry.RingedSite.tensorTotalMap_comp`. This is the iso whose
underlying morphism is pinned on local pure tensors by
`AlgebraicGeometry.RingedSite.tensorTotalMap_tensorTotalSection`, which is why it is stated here
rather than obtained from `AlgebraicGeometry.RingedSite.isIso_tensorTotalMap` by `asIso`. -/
@[simps]
def tensorTotalMapIso₂
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (e : B ≅ B') :
    tensorTotal X A B ≅ tensorTotal X A B' where
  hom := tensorTotalMap X (𝟙 A) e.hom
  inv := tensorTotalMap X (𝟙 A) e.inv
  hom_inv_id := by
    rw [tensorTotalMap_comp, e.hom_inv_id, Category.comp_id, tensorTotalMap_id]
  inv_hom_id := by
    rw [tensorTotalMap_comp, e.inv_hom_id, Category.comp_id, tensorTotalMap_id]

/-- **The total tensor complex commutes with the sign-free reindexing of its second factor.**
The reindexed second factor is turned into a shifted one, `Mathlib`'s comparison is applied, and
the shifted total complex is turned back into a reindexed one. -/
def tensorTotalReindexIso₂
    (A Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) :
    tensorTotal X A (CochainComplex.reindexBy Z k) ≅
      CochainComplex.reindexBy (tensorTotal X A Z) k :=
  tensorTotalMapIso₂ X A (CochainComplex.reindexByIsoShift Z k) ≪≫
    tensorTotalShiftIso₂ X A Z k ≪≫
    (CochainComplex.reindexByIsoShift (tensorTotal X A Z) k).symm

/-- **The sign-free comparison on a local pure tensor, with no sign.** The pure tensor of a
degree-`t` section of `A` with a degree-`r` section of `reindexBy Z k` — a degree-`k + r`
section of `Z` — is sent to the pure tensor of the same two sections, read in the degree
`k + (t + r)`.

The three signs of the proof cancel: `(-1)^{kr}` and `(-1)^{tk}` multiply to `(-1)^{k(t + r)}`
by `CochainComplex.negOnePow_shift_summand_cancel`, and that sign is paid twice. -/
lemma tensorTotalReindexIso₂_tensorTotalSection
    (A Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U))
    (b : ((CochainComplex.reindexBy Z k).X r).val.obj (op U)) :
    ((tensorTotalReindexIso₂ X A Z k).hom.f (t + r)).val.app (op U)
        (tensorTotalSection X A (CochainComplex.reindexBy Z k) U t r a b) =
      tensorTotalSectionAt X A Z U t (k + r) (k + (t + r)) (by omega) a b := by
  have hs : (k * (t + r)).negOnePow * (t * k).negOnePow * (k * r).negOnePow = 1 := by
    rw [mul_assoc, mul_comm ((t * k).negOnePow),
      CochainComplex.negOnePow_shift_summand_cancel, Int.units_mul_self]
  rw [tensorTotalReindexIso₂, Iso.trans_hom, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, comp_val_app_apply', comp_val_app_apply', tensorTotalMapIso₂_hom,
    tensorTotalMap_tensorTotalSection, tensorTotalShiftIso₂_tensorTotalSection,
    Iso.symm_hom, CochainComplex.reindexByIsoShift_inv_f, units_smul_val_app_apply,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    CochainComplex.reindexByIsoShift_hom_f, units_smul_val_app_apply,
    tensorTotalSectionAt_units_smul_right,
    tensorTotalSectionAt_congr_right X U t (r + k) (k + r) (t + r + k) (by omega) (by omega)
      (by omega)]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorTotalSectionAt_XIsoOfEq_inv, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul,
    hs, Units.val_one, one_smul]
  rfl

end AlgebraicGeometry.RingedSite

end
