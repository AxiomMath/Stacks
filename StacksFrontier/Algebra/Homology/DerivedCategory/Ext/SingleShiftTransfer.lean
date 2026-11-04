module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Morphisms between single objects in two degrees, read as `Ext`

Let `𝒜` be an abelian category with a derived category. A morphism
`φ : A[-d] ⟶ F[0]` of `D(𝒜)`, from `A` placed in degree `d` to `F` placed in degree `0`, is the
same as a morphism `A[0] ⟶ F[0]⟦d⟧`, that is an element of `Ext^d(A, F)`. This file records that
reading, `Stacks.DerivedCategoryExt.toExt`, together with two facts about it: it detects zero,
and precomposing `φ` with a morphism `v : A' ⟶ A` placed in degree `d` is the Yoneda product with
`v` in degree `0`.

Since `Ext` does not depend on the model of the derived category, this moves a statement about
such morphisms from one model of `D(𝒜)` to another: `toExt` in one model and
`CategoryTheory.Abelian.Ext.hom` in the other.

## Main definitions

* `Stacks.DerivedCategoryExt.toExt`: the element of `Ext^d(A, F)` attached to `φ : A[-d] ⟶ F[0]`.

## Main results

* `Stacks.DerivedCategoryExt.toExt_eq_zero_iff`: `toExt φ = 0 ↔ φ = 0`.
* `Stacks.DerivedCategoryExt.toExt_singleFunctor_map_comp`: `toExt (v[-d] ≫ φ)` is the product of
  `v` with `toExt φ`.
* `Stacks.DerivedCategoryExt.hom_eq_zero_iff` and `Stacks.DerivedCategoryExt.mk₀_comp_hom`: the
  same two facts for `Ext.hom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

universe w w' v u

namespace Stacks.DerivedCategoryExt

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Model

variable [HasDerivedCategory.{w'} C]

/-- `A` placed in degree `d`, shifted by `d`, is `A` placed in degree `0`. -/
def singleShiftIso (d : ℕ) (A : C) :
    ((singleFunctor C (d : ℤ)).obj A)⟦(d : ℤ)⟧ ≅ (singleFunctor C 0).obj A :=
  ((singleFunctors C).shiftIso (d : ℤ) 0 (d : ℤ) (by simp)).app A

omit [HasExt C] in
/-- The isomorphism `singleShiftIso` is natural in `A`. -/
theorem singleShiftIso_hom_naturality (d : ℕ) {A A' : C} (v : A' ⟶ A) :
    ((singleFunctor C (d : ℤ)).map v)⟦(d : ℤ)⟧' ≫ (singleShiftIso d A).hom =
      (singleShiftIso d A').hom ≫ (singleFunctor C 0).map v :=
  ((singleFunctors C).shiftIso (d : ℤ) 0 (d : ℤ) (by simp)).hom.naturality v

/-- **The element of `Ext^d(A, F)` attached to a morphism `A[-d] ⟶ F[0]`.** -/
def toExt {d : ℕ} {A F : C}
    (φ : (singleFunctor C (d : ℤ)).obj A ⟶ (singleFunctor C 0).obj F) : Abelian.Ext.{w} A F d :=
  Abelian.Ext.homEquiv.symm ((singleShiftIso d A).inv ≫ φ⟦(d : ℤ)⟧')

/-- Read in the derived category, `toExt φ` is `φ` shifted by `d`, precomposed with the inverse
of `singleShiftIso d A`. -/
theorem toExt_hom {d : ℕ} {A F : C}
    (φ : (singleFunctor C (d : ℤ)).obj A ⟶ (singleFunctor C 0).obj F) :
    (toExt φ).hom = (singleShiftIso d A).inv ≫ φ⟦(d : ℤ)⟧' :=
  Abelian.Ext.homEquiv.apply_symm_apply _

/-- `Ext.hom` detects zero. -/
theorem hom_eq_zero_iff {d : ℕ} {A F : C} (E : Abelian.Ext.{w} A F d) : E.hom = 0 ↔ E = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, Abelian.Ext.zero_hom]⟩
  ext
  rw [h, Abelian.Ext.zero_hom]

/-- **`toExt` detects zero.** -/
theorem toExt_eq_zero_iff {d : ℕ} {A F : C}
    (φ : (singleFunctor C (d : ℤ)).obj A ⟶ (singleFunctor C 0).obj F) :
    toExt.{w} φ = 0 ↔ φ = 0 := by
  rw [← hom_eq_zero_iff, toExt_hom, Preadditive.IsIso.comp_left_eq_zero, Functor.map_eq_zero_iff]

/-- **The product of `v` in degree `0` with `E`, read in the derived category, is
precomposition with `v` placed in degree `0`.** -/
theorem mk₀_comp_hom {d : ℕ} {A' A F : C} (v : A' ⟶ A) (E : Abelian.Ext.{w} A F d) :
    ((Abelian.Ext.mk₀ v).comp E (zero_add d)).hom = (singleFunctor C 0).map v ≫ E.hom := by
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]

/-- **The product of `v` in degree `0` with `E` vanishes exactly when precomposing `E`, read in the
derived category, with `v` placed in degree `0` does.** -/
theorem mk₀_comp_eq_zero_iff {d : ℕ} {A' A F : C} (v : A' ⟶ A) (E : Abelian.Ext.{w} A F d) :
    (Abelian.Ext.mk₀ v).comp E (zero_add d) = 0 ↔ (singleFunctor C 0).map v ≫ E.hom = 0 := by
  rw [← mk₀_comp_hom, hom_eq_zero_iff]

/-- **Precomposition in degree `d` is the product in degree `0`.** -/
theorem toExt_singleFunctor_map_comp {d : ℕ} {A' A F : C} (v : A' ⟶ A)
    (φ : (singleFunctor C (d : ℤ)).obj A ⟶ (singleFunctor C 0).obj F) :
    toExt.{w} ((singleFunctor C (d : ℤ)).map v ≫ φ) =
      (Abelian.Ext.mk₀ v).comp (toExt φ) (zero_add d) := by
  ext
  rw [mk₀_comp_hom, toExt_hom, toExt_hom, Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← singleShiftIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end Model

end Stacks.DerivedCategoryExt
