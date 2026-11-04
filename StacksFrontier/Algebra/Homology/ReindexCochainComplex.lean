module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Reindexing a cochain complex by a translation, without signs

Let `F` be a cochain complex in a category with zero morphisms and let `k` be an integer. This
file defines the complex `n ↦ F^{k + n}` whose differentials are those of `F`, with no sign.

This is not the shift `F⟦k⟧`, which is indexed by `n + k` and whose differentials carry the sign
`(-1)^k`. In a preadditive category the two are isomorphic, by the identity on terms twisted by
the sign `(-1)^{kn}`.

## Main definitions

* `CochainComplex.reindexBy`: the complex `n ↦ F^{k + n}`, with the differentials of `F`.
* `CochainComplex.reindexByIsoShift`: the isomorphism `reindexBy F k ≅ F⟦k⟧` given in degree `n`
  by `(-1)^{kn}` times the identification `F^{k + n} ≅ F^{n + k}`.

## Main results

* `CochainComplex.reindexByIsoShift_hom_f`, `CochainComplex.reindexByIsoShift_inv_f`: the
  components of `reindexByIsoShift` and of its inverse.
* `CochainComplex.negOnePow_shift_summand_cancel`: the identity
  `(-1)^{kq} · (-1)^{pk} = (-1)^{k(p + q)}`.

## Implementation notes

The construction of `reindexBy` needs only `HasZeroMorphisms`; additivity is needed in
`reindexByIsoShift` only to multiply a morphism by a sign.

`reindexBy` is an `abbrev` so that the terms of `reindexBy F k` are recognised at `implicit`
transparency as the terms `F.X (k + n)` of `F`.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

/-- The reindexing of a cochain complex `F` by an integer `k`: the cochain complex whose term in
degree `n` is `F^{k + n}` and whose differentials are those of `F`, with no sign. -/
abbrev reindexBy {A : Type*} [Category A] [Limits.HasZeroMorphisms A]
    (F : CochainComplex A ℤ) (k : ℤ) : CochainComplex A ℤ where
  X n := F.X (k + n)
  d n m := F.d (k + n) (k + m)
  shape i j hij := F.shape _ _ (by
    simp only [ComplexShape.up_Rel] at hij ⊢
    omega)
  d_comp_d' i j l _ _ := F.d_comp_d _ _ _

/-- The term of `reindexBy F k` in degree `n` is `F.X (k + n)`. -/
@[simp]
lemma reindexBy_X {A : Type*} [Category A] [Limits.HasZeroMorphisms A]
    (F : CochainComplex A ℤ) (k n : ℤ) : (reindexBy F k).X n = F.X (k + n) := rfl

/-- The differential of `reindexBy F k` from degree `n` to degree `m` is `F.d (k + n) (k + m)`. -/
@[simp]
lemma reindexBy_d {A : Type*} [Category A] [Limits.HasZeroMorphisms A]
    (F : CochainComplex A ℤ) (k n m : ℤ) :
    (reindexBy F k).d n m = F.d (k + n) (k + m) := rfl

/-- The isomorphism between the reindexing `reindexBy F k` and the shift `F⟦k⟧`, given in degree
`n` by `(-1)^{kn}` times the identification `F^{k + n} ≅ F^{n + k}`. -/
noncomputable def reindexByIsoShift {A : Type*} [Category A] [Preadditive A]
    (F : CochainComplex A ℤ) (k : ℤ) :
    reindexBy F k ≅ (CategoryTheory.shiftFunctor (CochainComplex A ℤ) k).obj F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := (k * n).negOnePow • (F.XIsoOfEq (by omega : k + n = n + k)).hom
        inv := (k * n).negOnePow • (F.XIsoOfEq (by omega : k + n = n + k)).inv
        hom_inv_id := by
          rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
            Int.units_mul_self, one_smul, Iso.hom_inv_id]
        inv_hom_id := by
          rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
            Int.units_mul_self, one_smul, Iso.inv_hom_id] })
    (fun i j hij => by
      obtain rfl : j = i + 1 := by
        simp only [ComplexShape.up_Rel] at hij
        omega
      simp only [CochainComplex.shiftFunctor_obj_d', Linear.units_smul_comp,
        Linear.comp_units_smul, smul_smul, HomologicalComplex.XIsoOfEq_hom_comp_d,
        HomologicalComplex.d_comp_XIsoOfEq_hom]
      congr 1
      rw [mul_add, mul_one, Int.negOnePow_add]
      exact mul_comm _ _)

/-- The component of `reindexByIsoShift F k` in degree `n` is `(-1)^{kn}` times the
identification `F^{k + n} ≅ F^{n + k}`. -/
lemma reindexByIsoShift_hom_f {A : Type*} [Category A] [Preadditive A]
    (F : CochainComplex A ℤ) (k n : ℤ) :
    (reindexByIsoShift F k).hom.f n =
      (k * n).negOnePow • (F.XIsoOfEq (by omega : k + n = n + k)).hom :=
  rfl

/-- The component of the inverse of `reindexByIsoShift F k` in degree `n` is `(-1)^{kn}` times
the identification `F^{n + k} ≅ F^{k + n}`. -/
lemma reindexByIsoShift_inv_f {A : Type*} [Category A] [Preadditive A]
    (F : CochainComplex A ℤ) (k n : ℤ) :
    (reindexByIsoShift F k).inv.f n =
      (k * n).negOnePow • (F.XIsoOfEq (by omega : k + n = n + k)).inv :=
  rfl

/-- For integers `k`, `p`, `q`, the signs satisfy `(-1)^{kq} · (-1)^{pk} = (-1)^{k(p + q)}`. -/
lemma negOnePow_shift_summand_cancel (k p q : ℤ) :
    (k * q).negOnePow * (p * k).negOnePow = (k * (p + q)).negOnePow := by
  rw [mul_add, Int.negOnePow_add, mul_comm p k, mul_comm]

end CochainComplex

end
