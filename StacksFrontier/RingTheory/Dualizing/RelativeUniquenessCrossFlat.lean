module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import Mathlib.RingTheory.Flat.Stability

/-!
# Base change along one coprojection, read along the other

Let `R → A` be a ring map and `B = A ⊗[R] A`, with coprojections `p₁, p₂ : A → B`. For an
`A`-module `M` the extension of scalars `B ⊗_{A, p₁} M`, regarded as an `A`-module through `p₂`,
is the base change `A ⊗[R] M` of the underlying `R`-module of `M`: the element
`(a₁ ⊗ a₂) ⊗ m` corresponds to `a₂ ⊗ a₁ m`. In particular it is flat over `A` as soon as `M` is
flat over `R`. The same holds with the two coprojections exchanged.

## Main results

* `Dualizing.CrossFlat.flat_restrictScalars_tensorProduct` — the statement for an arbitrary
  presentation of `B` as `A ⊗[R] A`.
* `Dualizing.CrossFlat.flat_restrictScalars_includeRight_extendScalars_includeLeft` and
  `Dualizing.CrossFlat.flat_restrictScalars_includeLeft_extendScalars_includeRight` — the two
  coprojections.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Dualizing.CrossFlat

section Generic

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  (q : A →+* B) (μ : A ⊗[R] A ≃+* B) (hμl : ∀ a : A, μ (a ⊗ₜ 1) = algebraMap A B a)
  (hμr : ∀ a : A, μ (1 ⊗ₜ a) = q a)
  (M : Type u) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/-- `a₁ ⊗ a₂ ↦ a₂ ⊗ a₁ m`. -/
noncomputable def aux (m : M) : A ⊗[R] A →+ A ⊗[R] M :=
  (TensorProduct.lift (LinearMap.mk₂ R (fun (a₁ a₂ : A) => a₂ ⊗ₜ[R] (a₁ • m))
    (fun _ _ _ => by simp [add_smul, TensorProduct.tmul_add])
    (fun _ _ _ => by simp [smul_assoc, TensorProduct.tmul_smul])
    (fun _ _ _ => TensorProduct.add_tmul _ _ _)
    (fun _ _ _ => by simp [TensorProduct.smul_tmul']))).toAddMonoidHom

/-- The map `aux m` sends `a₁ ⊗ a₂` to `a₂ ⊗ (a₁ • m)`. -/
@[simp] lemma aux_tmul (m : M) (a₁ a₂ : A) :
    aux (R := R) M m (a₁ ⊗ₜ a₂) = a₂ ⊗ₜ[R] (a₁ • m) := rfl

/-- `aux m ((x ⊗ 1) * t) = aux (x • m) t`. -/
lemma aux_mul (m : M) (x : A) (t : A ⊗[R] A) :
    aux (R := R) M m ((x ⊗ₜ 1) * t) = aux M (x • m) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a₁ a₂ =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, aux_tmul, smul_smul, mul_comm]
  | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz]

include hμl hμr in
/-- The two maps `A → B`, `q` and `algebraMap A B`, agree on the image of `R`. -/
lemma algebraMap_eq (r : R) : q (algebraMap R A r) = algebraMap A B (algebraMap R A r) := by
  rw [← hμr, ← hμl]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- `a ⊗ m ↦ q(a) ⊗ m`. -/
noncomputable def toTensor : A ⊗[R] M →+ B ⊗[A] M :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun m => q a ⊗ₜ[A] m
          map_zero' := by simp
          map_add' := fun m m' => TensorProduct.tmul_add _ _ _ }
      map_zero' := by ext; simp
      map_add' := fun a a' => by ext; simp [TensorProduct.add_tmul] }
    (fun r a m => by
      change q (r • a) ⊗ₜ[A] m = q a ⊗ₜ[A] (r • m)
      rw [← IsScalarTower.algebraMap_smul A r m, ← TensorProduct.smul_tmul, Algebra.smul_def,
        Algebra.smul_def, map_mul, algebraMap_eq q μ hμl hμr])

/-- `toTensor` sends `a ⊗ m` to `q a ⊗ m`. -/
@[simp] lemma toTensor_tmul (a : A) (m : M) :
    toTensor (R := R) q μ hμl hμr M (a ⊗ₜ m) = q a ⊗ₜ[A] m := rfl

/-- `b ⊗ m ↦ a₂ ⊗ a₁ m` for `μ⁻¹(b) = a₁ ⊗ a₂`. -/
noncomputable def fromTensor : B ⊗[A] M →+ A ⊗[R] M :=
  TensorProduct.liftAddHom
    { toFun := fun b =>
        { toFun := fun m => aux (R := R) M m (μ.symm b)
          map_zero' := by
            induction μ.symm b using TensorProduct.induction_on with
            | zero => simp
            | tmul => simp
            | add y z hy hz => rw [map_add, hy, hz, add_zero]
          map_add' := fun m m' => by
            induction μ.symm b using TensorProduct.induction_on with
            | zero => simp
            | tmul => simp [smul_add, TensorProduct.tmul_add]
            | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]; abel }
      map_zero' := by ext; simp
      map_add' := fun b b' => by ext; simp }
    (fun x b m => by
      change aux M m (μ.symm (x • b)) = aux M (x • m) (μ.symm b)
      rw [Algebra.smul_def, map_mul, ← hμl, RingEquiv.symm_apply_apply, aux_mul])

/-- `fromTensor` is a left inverse of `toTensor`. -/
lemma fromTensor_toTensor (z : A ⊗[R] M) :
    fromTensor (R := R) μ hμl M (toTensor q μ hμl hμr M z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    show aux M m (μ.symm (q a)) = a ⊗ₜ m
    rw [← hμr, RingEquiv.symm_apply_apply, aux_tmul, one_smul]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- `fromTensor` is a right inverse of `toTensor`. -/
lemma toTensor_fromTensor (z : B ⊗[A] M) :
    toTensor q μ hμl hμr M (fromTensor (R := R) μ hμl M z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    show toTensor q μ hμl hμr M (aux M m (μ.symm b)) = b ⊗ₜ m
    obtain ⟨t, rfl⟩ := μ.surjective b
    rw [RingEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      rw [aux_tmul, toTensor_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, ← hμl, ← hμr,
        ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, TensorProduct.add_tmul]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- `toTensor` is `A`-linear when `B ⊗[A] M` is regarded as an `A`-module through `q`. -/
lemma toTensor_smul (x : A) (z : A ⊗[R] M) :
    toTensor q μ hμl hμr M (x • z) = q x • toTensor q μ hμl hμr M z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a m =>
    show q (x * a) ⊗ₜ[A] m = q x • (q a ⊗ₜ[A] m)
    rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add y z hy hz => rw [smul_add, map_add, hy, hz, map_add, smul_add]

/-- `B ⊗[A] M`, read as an `A`-module through `q`, is the base change `A ⊗[R] M`. -/
noncomputable def linearEquiv :
    A ⊗[R] M ≃ₗ[A] (ModuleCat.restrictScalars q).obj (ModuleCat.of B (B ⊗[A] M)) where
  toFun := toTensor q μ hμl hμr M
  invFun := fromTensor (R := R) μ hμl M
  left_inv := fromTensor_toTensor q μ hμl hμr M
  right_inv := toTensor_fromTensor q μ hμl hμr M
  map_add' := map_add _
  map_smul' := fun x z => (toTensor_smul q μ hμl hμr M x z).trans
    (ModuleCat.restrictScalars.smul_def q (M := ModuleCat.of B (B ⊗[A] M)) x _).symm

include μ hμl hμr in
/-- **`B ⊗[A] M`, read through `q`, is flat over `A` when `M` is flat over `R`.** -/
theorem flat_restrictScalars_tensorProduct [Module.Flat R M] :
    Module.Flat A ((ModuleCat.restrictScalars q).obj (ModuleCat.of B (B ⊗[A] M))) :=
  Module.Flat.of_linearEquiv (linearEquiv q μ hμl hμr M).symm

end Generic


section Coprojections

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (M : ModuleCat.{u} A)

/-- Flatness of `B ⊗[A] M` read through `q`, for an `A`-module `M` flat over `R`. -/
private theorem flat_restrictScalars_extendScalars_of_flat {B : Type u} [CommRing B] [Algebra A B]
    (q : A →+* B) (μ : A ⊗[R] A ≃+* B) (hμl : ∀ a : A, μ (a ⊗ₜ 1) = algebraMap A B a)
    (hμr : ∀ a : A, μ (1 ⊗ₜ a) = q a)
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)) :
    Module.Flat A ((ModuleCat.restrictScalars q).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)) := by
  let : Module R M := ((ModuleCat.restrictScalars (algebraMap R A)).obj M).isModule
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R M := hM
  have := flat_restrictScalars_tensorProduct q μ hμl hμr M
  exact Module.Flat.of_linearEquiv ((ModuleCat.restrictScalars q).mapIso
    (PseudoCoherence.extendScalarsAlgebraMapObjIso (R := A) (S := B) M)).toLinearEquiv

/-- **Base change along the left coprojection, read along the right one, is flat** over `A`
for every `A`-module flat over `R`. -/
theorem flat_restrictScalars_includeRight_extendScalars_includeLeft
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)) :
    Module.Flat A ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj M)) :=
  flat_restrictScalars_extendScalars_of_flat R A M
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
    (RingEquiv.refl (A ⊗[R] A)) (fun _ => rfl) (fun _ => rfl) hM

/-- **Base change along the right coprojection, read along the left one, is flat** over `A`
for every `A`-module flat over `R`. -/
theorem flat_restrictScalars_includeLeft_extendScalars_includeRight
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)) :
    Module.Flat A ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).obj M)) := by
  let : Algebra A (A ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  exact flat_restrictScalars_extendScalars_of_flat R A M
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
    (Algebra.TensorProduct.comm R A A).toRingEquiv (fun _ => rfl) (fun _ => rfl) hM

end Coprojections

end Dualizing.CrossFlat
