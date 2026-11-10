module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection

/-!
# Morphisms of free sheaves of modules of finite rank are matrices of global functions

Let `X` be a scheme and `𝒪_X^a` the free sheaf of `𝒪_X`-modules of rank `a`. A morphism
`φ : 𝒪_X^a ⟶ 𝒪_X^b` is determined by the images of the `a` basis sections, each of which is a
`b`-tuple of global functions; this file makes that precise. The matrix of `φ` has the
coordinates of the image of the `j`-th basis section in its `j`-th column, so that composition
of morphisms is the matrix product in the reverse order, `M(φ ≫ ψ) = M(ψ) * M(φ)`.

## Main definitions

* `Stacks.FreeSheafMatrix.unitEndEquiv`: the endomorphisms of `𝒪_X` are the global functions.
* `Stacks.FreeSheafMatrix.toMatrix`: the matrix of a morphism `𝒪_X^a ⟶ 𝒪_X^b`, a
  `b × a` matrix over `Γ(X, 𝒪_X)`.
* `Stacks.FreeSheafMatrix.ofMatrix`: the morphism of a matrix.

## Main results

* `Stacks.FreeSheafMatrix.toMatrix_ofMatrix` and `Stacks.FreeSheafMatrix.ofMatrix_toMatrix`:
  the two constructions are mutually inverse.
* `Stacks.FreeSheafMatrix.toMatrix_comp`: composition is the reversed matrix product.
* `Stacks.FreeSheafMatrix.toMatrix_id` and `Stacks.FreeSheafMatrix.toMatrix_freeMap`: the
  identity and the coordinate maps.
* `Stacks.FreeSheafMatrix.isIso_iff_isUnit_det`: an endomorphism of `𝒪_X^m` is an isomorphism
  exactly when the determinant of its matrix is a unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.FreeSheafMatrix

variable (X : Scheme.{u})

/-- The free sheaf of `𝒪_X`-modules of rank `a`. -/
abbrev F (a : ℕ) : SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin a))

/-! ### Endomorphisms of the structure sheaf -/

variable {X}

/-- The global function attached to an endomorphism of `𝒪_X`: the image of `1`. -/
def unitEndValue (t : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Γ(X, ⊤) :=
  ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv t).1 (op ⊤)

/-- The global section of `𝒪_X`, as a sheaf of modules, attached to a global function. -/
def unitSection (r : Γ(X, ⊤)) : (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun U => X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
    (by
      intro U V f
      change X.presheaf.map f _ = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The endomorphism of `𝒪_X` given by multiplication by a global function. -/
def scalarEnd (r : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (unitSection r)

/-- Multiplication by a global function `r` sends `1` to `r`. -/
theorem unitEndValue_scalarEnd (r : Γ(X, ⊤)) : unitEndValue (scalarEnd r) = r := by
  change (((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (unitSection r))).1 (op ⊤)) = r
  rw [Equiv.apply_symm_apply]
  change X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op r = r
  rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- An endomorphism of `𝒪_X` is multiplication by the image of `1`. -/
theorem scalarEnd_unitEndValue
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    scalarEnd (unitEndValue t) = t := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  rw [scalarEnd, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  exact ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv t).2
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op

/-- **The endomorphisms of `𝒪_X` are the global functions.** -/
def unitEndEquiv :
    (SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ Γ(X, ⊤) where
  toFun := unitEndValue
  invFun := scalarEnd
  left_inv := scalarEnd_unitEndValue
  right_inv := unitEndValue_scalarEnd

/-- An endomorphism of `𝒪_X` is determined by the image of `1`. -/
theorem unitEndValue_injective : Function.Injective (unitEndValue (X := X)) :=
  unitEndEquiv.injective

/-- The global function of a composite of endomorphisms of `𝒪_X` is the product of their global
functions. -/
theorem unitEndValue_comp
    (s t : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    unitEndValue (s ≫ t) = unitEndValue s * unitEndValue t := by
  have key : ∀ (f : X.ringCatSheaf.obj.obj (op ⊤) →ₗ[X.ringCatSheaf.obj.obj (op ⊤)]
      X.ringCatSheaf.obj.obj (op ⊤)) (x : X.ringCatSheaf.obj.obj (op ⊤)), f x = x * f 1 :=
    fun f x => by rw [← smul_eq_mul, ← f.map_smul, smul_eq_mul, mul_one]
  exact key (t.val.app (op ⊤)).hom (unitEndValue s)

/-- The global function of the identity of `𝒪_X` is `1`. -/
theorem unitEndValue_id : unitEndValue (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 1 := rfl

/-- The global function of the zero endomorphism of `𝒪_X` is `0`. -/
theorem unitEndValue_zero :
    unitEndValue
      (0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) = 0 :=
  rfl

/-- The global function of a sum of endomorphisms of `𝒪_X` is the sum of their global functions. -/
theorem unitEndValue_add
    (s t : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    unitEndValue (s + t) = unitEndValue s + unitEndValue t := rfl

/-- The global function of a finite sum of endomorphisms of `𝒪_X` is the sum of their global
functions. -/
theorem unitEndValue_sum {ι : Type*} (S : Finset ι)
    (f : ι → (SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)) :
    unitEndValue (∑ i ∈ S, f i) = ∑ i ∈ S, unitEndValue (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [unitEndValue_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, unitEndValue_add, ih]

/-! ### The matrix of a morphism -/

/-- **The matrix of a morphism `𝒪_X^a ⟶ 𝒪_X^b`**: its `(i, j)` entry is the `i`-th coordinate of
the image of the `j`-th basis section. -/
def toMatrix {a b : ℕ} (φ : F X a ⟶ F X b) : Matrix (Fin b) (Fin a) Γ(X, ⊤) :=
  fun i j => unitEndValue (SheafOfModules.ιFree (ULift.up j) ≫ φ ≫
    SheafOfModules.freeProjection (ULift.up i))

/-- The `(i, j)` entry of `toMatrix φ` is the global function of the composite of the `j`-th
inclusion, `φ`, and the `i`-th projection. -/
theorem toMatrix_apply {a b : ℕ} (φ : F X a ⟶ F X b) (i : Fin b) (j : Fin a) :
    toMatrix φ i j = unitEndValue (SheafOfModules.ιFree (R := X.ringCatSheaf)
      (ULift.up.{u} j) ≫ φ ≫ SheafOfModules.freeProjection (ULift.up.{u} i)) := rfl

/-- **The morphism `𝒪_X^a ⟶ 𝒪_X^b` of a matrix**: the `j`-th basis section goes to the section
whose coordinates are the `j`-th column. -/
def ofMatrix {a b : ℕ} (M : Matrix (Fin b) (Fin a) Γ(X, ⊤)) : F X a ⟶ F X b :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) _)
    fun j => ∑ i : ULift.{u} (Fin b), scalarEnd (M i.down j.down) ≫ SheafOfModules.ιFree i

/-- The restriction of `ofMatrix M` to the `j`-th summand is the sum over `i` of multiplication by
`M i j` followed by the `i`-th inclusion. -/
theorem ιFree_ofMatrix {a b : ℕ} (M : Matrix (Fin b) (Fin a) Γ(X, ⊤)) (j : Fin a) :
    SheafOfModules.ιFree (ULift.up j) ≫ ofMatrix M =
      ∑ i : ULift.{u} (Fin b), scalarEnd (M i.down j) ≫ SheafOfModules.ιFree i :=
  Cofan.IsColimit.fac _ _ (ULift.up j)

/-- The `i'`-th inclusion followed by the `i`-th projection of `𝒪_X^b` is multiplication by `1` if
`i' = i` and by `0` otherwise. -/
theorem ιFree_comp_freeProjection_value {b : ℕ} (i i' : Fin b) :
    unitEndValue (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i') ≫
        SheafOfModules.freeProjection (ULift.up i)) = if i' = i then 1 else 0 := by
  by_cases h : i' = i
  · subst h
    rw [SheafOfModules.ιFree_comp_freeProjection_self, ite_eq_left rfl]
    rfl
  · rw [SheafOfModules.ιFree_comp_freeProjection_of_ne (by simpa using h), ite_eq_right h]
    rfl

/-- The matrix of the morphism of a matrix `M` is `M`. -/
theorem toMatrix_ofMatrix {a b : ℕ} (M : Matrix (Fin b) (Fin a) Γ(X, ⊤)) :
    toMatrix (ofMatrix M) = M := by
  funext i j
  rw [toMatrix_apply, ← Category.assoc, ιFree_ofMatrix, Preadditive.sum_comp, unitEndValue_sum,
    Finset.sum_eq_single (ULift.up i)]
  · rw [Category.assoc, unitEndValue_comp, ιFree_comp_freeProjection_value, ite_eq_left rfl,
      mul_one, unitEndValue_scalarEnd]
  · intro i' _ hi'
    rw [Category.assoc, unitEndValue_comp, ιFree_comp_freeProjection_value,
      ite_eq_right (fun h => hi' (by rw [← h])), mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The morphism of the matrix of a morphism `φ` is `φ`. -/
theorem ofMatrix_toMatrix {a b : ℕ} (φ : F X a ⟶ F X b) : ofMatrix (toMatrix φ) = φ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) _)
    _ _ fun j => ?_
  change SheafOfModules.ιFree j ≫ ofMatrix (toMatrix φ) = SheafOfModules.ιFree j ≫ φ
  obtain ⟨j⟩ := j
  rw [ιFree_ofMatrix]
  have h : ∀ i : ULift.{u} (Fin b), scalarEnd (toMatrix φ i.down j) ≫ SheafOfModules.ιFree i =
      SheafOfModules.ιFree (ULift.up j) ≫ φ ≫ SheafOfModules.freeProjection i ≫
        SheafOfModules.ιFree i := by
    intro i
    rw [toMatrix_apply, scalarEnd_unitEndValue]
    simp only [Category.assoc]
  simp_rw [h]
  rw [← Preadditive.comp_sum, ← Preadditive.comp_sum,
    SheafOfModules.sum_freeProjection_comp_ιFree, Category.comp_id]

/-- **Morphisms `𝒪_X^a ⟶ 𝒪_X^b` are `b × a` matrices of global functions.** -/
def toMatrixEquiv (a b : ℕ) : (F X a ⟶ F X b) ≃ Matrix (Fin b) (Fin a) Γ(X, ⊤) where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv := ofMatrix_toMatrix
  right_inv := toMatrix_ofMatrix

/-- A morphism `𝒪_X^a ⟶ 𝒪_X^b` is determined by its matrix. -/
theorem toMatrix_injective {a b : ℕ} : Function.Injective (toMatrix (X := X) (a := a) (b := b)) :=
  (toMatrixEquiv a b).injective

/-- **Composition is the matrix product, in the reverse order.** -/
theorem toMatrix_comp {a b c : ℕ} (φ : F X a ⟶ F X b) (ψ : F X b ⟶ F X c) :
    toMatrix (φ ≫ ψ) = toMatrix ψ * toMatrix φ := by
  funext i j
  rw [Matrix.mul_apply, toMatrix_apply]
  have h : SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up j) ≫ (φ ≫ ψ) ≫
      SheafOfModules.freeProjection (ULift.up i) =
      ∑ l : ULift.{u} (Fin b), (SheafOfModules.ιFree (ULift.up j) ≫ φ ≫
        SheafOfModules.freeProjection l) ≫ (SheafOfModules.ιFree l ≫ ψ ≫
          SheafOfModules.freeProjection (ULift.up i)) := by
    conv_lhs => rw [← Category.id_comp ψ, ← SheafOfModules.sum_freeProjection_comp_ιFree]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [h, unitEndValue_sum]
  refine Fintype.sum_equiv Equiv.ulift _ _ fun l => ?_
  rw [unitEndValue_comp, mul_comm, toMatrix_apply, toMatrix_apply]
  rfl

/-- The matrix of the identity of `𝒪_X^a` is the identity matrix. -/
theorem toMatrix_id (a : ℕ) : toMatrix (𝟙 (F X a)) = 1 := by
  funext i j
  rw [toMatrix_apply, Category.id_comp, ιFree_comp_freeProjection_value, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- The matrix of the coordinate map `𝒪_X^a ⟶ 𝒪_X^b` attached to a map of index sets. -/
theorem toMatrix_freeMap {a b : ℕ} (f : Fin a → Fin b) :
    toMatrix (SheafOfModules.freeMap (R := X.ringCatSheaf)
      (fun j : ULift.{u} (Fin a) => ULift.up (f j.down))) =
      Matrix.of fun i j => if f j = i then 1 else 0 := by
  funext i j
  rw [toMatrix_apply, ← Category.assoc, SheafOfModules.ιFree_freeMap,
    ιFree_comp_freeProjection_value, Matrix.of_apply]

/-- **An endomorphism of `𝒪_X^m` is an isomorphism exactly when the determinant of its matrix is a
unit.** -/
theorem isIso_iff_isUnit_det {m : ℕ} (φ : F X m ⟶ F X m) :
    IsIso φ ↔ IsUnit (toMatrix φ).det := by
  constructor
  · intro hφ
    exact Matrix.isUnit_det_of_right_inverse (B := toMatrix (inv φ))
      (by rw [← toMatrix_comp, IsIso.inv_hom_id, toMatrix_id])
  · intro hdet
    refine ⟨ofMatrix (toMatrix φ)⁻¹, toMatrix_injective ?_, toMatrix_injective ?_⟩
    · rw [toMatrix_comp, toMatrix_ofMatrix, toMatrix_id, Matrix.nonsing_inv_mul _ hdet]
    · rw [toMatrix_comp, toMatrix_ofMatrix, toMatrix_id, Matrix.mul_nonsing_inv _ hdet]

end Stacks.FreeSheafMatrix

end
