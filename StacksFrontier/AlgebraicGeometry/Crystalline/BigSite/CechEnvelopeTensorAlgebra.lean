module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts

/-!
# Finite tensor products of smooth algebras, and their base change

Algebraic lemmas for the base change of the Čech envelopes of smooth lifts
(`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/CechEnvelopeChangeBase.lean`).

## Main results

* `CechEnvelope.smooth_piTensorProduct` — a finite tensor product `B_0 ⊗_R ⋯ ⊗_R B_n` of smooth
  `R`-algebras is smooth, by induction through `piTensorFinSuccEquiv`,
  `⨂_{i < n + 2} B_i ≅ B_0 ⊗ ⨂_{j < n + 1} B_{j + 1}`.
* `CechEnvelope.piTensor_ringHom_ext` — ring maps out of a finite tensor product of algebras are
  determined on the base and on the factors.
* `CechEnvelope.piTensorBaseChangeEquiv` — `A ⊗_R ⨂_R B_i ≅ ⨂_A (A ⊗_R B_i)`.
* `CechEnvelope.isBaseChange_restrictScalars_of_isPushout` — if `R = A ⊗_{A'} R'` and
  `N = R ⊗_{R'} M'`, then `N = A ⊗_{A'} M'`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

section Smooth

variable (R : Type u) [CommRing R]

/-- `⨂_{i < 1} B_i ≅ B_0`. -/
def piTensorFinOneEquiv (B : Fin 1 → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] :
    (⨂[R] i, B i) ≃ₐ[R] B 0 :=
  AlgEquiv.ofAlgHom
    (piLift fun i ↦ Fin.cases (motive := fun i ↦ B i →ₐ[R] B 0) (AlgHom.id R (B 0))
      (fun j ↦ j.elim0) i)
    (PiTensorProduct.singleAlgHom 0)
    (AlgHom.ext fun b ↦ piLift_single _ 0 b)
    (PiTensorProduct.algHom_ext fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ j.elim0) i
      exact AlgHom.ext fun b ↦ congrArg (PiTensorProduct.singleAlgHom 0) (piLift_single _ 0 b))

section Succ

variable {n : ℕ} (B : Fin (n + 2) → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- The tensor product of the last `n + 1` factors. -/
abbrev piTensorTail : Type u := ⨂[R] (j : Fin (n + 1)), B j.succ

/-- `⨂_{i < n + 2} B_i → B_0 ⊗ ⨂_{j < n + 1} B_{j + 1}`. -/
def piTensorFinSuccHom : (⨂[R] i, B i) →ₐ[R] B 0 ⊗[R] piTensorTail R B :=
  piLift fun i ↦ Fin.cases (motive := fun i ↦ B i →ₐ[R] B 0 ⊗[R] piTensorTail R B)
    Algebra.TensorProduct.includeLeft
    (fun j ↦ Algebra.TensorProduct.includeRight.comp
      (PiTensorProduct.singleAlgHom (R := R) (A := fun j : Fin (n + 1) ↦ B j.succ) j)) i

/-- `piTensorFinSuccHom` on the first factor. -/
theorem piTensorFinSuccHom_single_zero (b : B 0) :
    piTensorFinSuccHom R B (PiTensorProduct.singleAlgHom 0 b) = b ⊗ₜ 1 :=
  piLift_single _ 0 b

/-- `piTensorFinSuccHom` on the other factors. -/
theorem piTensorFinSuccHom_single_succ (j : Fin (n + 1)) (b : B j.succ) :
    piTensorFinSuccHom R B (PiTensorProduct.singleAlgHom j.succ b) =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := R) (A := fun j : Fin (n + 1) ↦ B j.succ) j b :=
  piLift_single _ j.succ b

/-- `B_0 ⊗ ⨂_{j < n + 1} B_{j + 1} → ⨂_{i < n + 2} B_i`. -/
def piTensorFinSuccInv : B 0 ⊗[R] piTensorTail R B →ₐ[R] ⨂[R] i, B i :=
  Algebra.TensorProduct.lift (PiTensorProduct.singleAlgHom 0)
    (piLift fun j ↦ PiTensorProduct.singleAlgHom (R := R) (A := B) j.succ)
    fun _ _ ↦ Commute.all _ _

/-- `piTensorFinSuccInv` on a pure tensor. -/
theorem piTensorFinSuccInv_tmul (b : B 0) (t : piTensorTail R B) :
    piTensorFinSuccInv R B (b ⊗ₜ t) = PiTensorProduct.singleAlgHom 0 b *
      piLift (fun j ↦ PiTensorProduct.singleAlgHom (R := R) (A := B) j.succ) t :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `⨂_{i < n + 2} B_i ≅ B_0 ⊗ ⨂_{j < n + 1} B_{j + 1}`. -/
def piTensorFinSuccEquiv : (⨂[R] i, B i) ≃ₐ[R] B 0 ⊗[R] piTensorTail R B :=
  AlgEquiv.ofAlgHom (piTensorFinSuccHom R B) (piTensorFinSuccInv R B)
    (by
      refine Algebra.TensorProduct.ext' fun b t ↦ ?_
      change piTensorFinSuccHom R B (piTensorFinSuccInv R B (b ⊗ₜ t)) = b ⊗ₜ t
      rw [piTensorFinSuccInv_tmul, map_mul, piTensorFinSuccHom_single_zero]
      have ht : (piTensorFinSuccHom R B).comp
          (piLift fun j ↦ PiTensorProduct.singleAlgHom (R := R) (A := B) j.succ) =
          Algebra.TensorProduct.includeRight := by
        refine PiTensorProduct.algHom_ext fun j ↦ AlgHom.ext fun b' ↦ ?_
        change piTensorFinSuccHom R B (piLift _ (PiTensorProduct.singleAlgHom (R := R)
          (A := fun j : Fin (n + 1) ↦ B j.succ) j b')) = _
        rw [piLift_single, piTensorFinSuccHom_single_succ]
        rfl
      rw [show piTensorFinSuccHom R B (piLift (fun j ↦ PiTensorProduct.singleAlgHom (R := R)
          (A := B) j.succ) t) = 1 ⊗ₜ t from AlgHom.congr_fun ht t,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul])
    (PiTensorProduct.algHom_ext fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · refine AlgHom.ext fun b ↦ ?_
        change piTensorFinSuccInv R B (piTensorFinSuccHom R B
          (PiTensorProduct.singleAlgHom 0 b)) = PiTensorProduct.singleAlgHom 0 b
        rw [piTensorFinSuccHom_single_zero, piTensorFinSuccInv_tmul, map_one, mul_one]
      · refine AlgHom.ext fun b ↦ ?_
        change piTensorFinSuccInv R B (piTensorFinSuccHom R B
          (PiTensorProduct.singleAlgHom j.succ b)) = PiTensorProduct.singleAlgHom j.succ b
        rw [piTensorFinSuccHom_single_succ, piTensorFinSuccInv_tmul, map_one, one_mul,
          piLift_single])

end Succ

/-- **A finite tensor product of smooth algebras is smooth.** -/
theorem smooth_piTensorProduct : ∀ (n : ℕ) (B : Fin (n + 1) → Type u) [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, Algebra.Smooth R (B i)], Algebra.Smooth R (⨂[R] i, B i)
  | 0, B, _, _, _ => Algebra.Smooth.of_equiv (piTensorFinOneEquiv R B).symm
  | n + 1, B, _, _, _ => by
    have := smooth_piTensorProduct n (fun j ↦ B j.succ)
    have : Algebra.Smooth R (B 0 ⊗[R] piTensorTail R B) :=
      Algebra.Smooth.comp R (B 0) _
    exact Algebra.Smooth.of_equiv (piTensorFinSuccEquiv R B).symm

end Smooth

/-! ### Ring maps out of a finite tensor product -/

section RingHomExt

variable {R : Type u} [CommRing R] {ι : Type} [Finite ι] [DecidableEq ι] {B : ι → Type u}
  [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] {T : Type*} [CommRing T]

/-- Two ring maps out of a finite tensor product of algebras agree as soon as they agree on the
base ring and on every factor. -/
theorem piTensor_ringHom_ext {φ ψ : (⨂[R] i, B i) →+* T}
    (hR : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _))
    (h : ∀ i, φ.comp (PiTensorProduct.singleAlgHom (R := R) (A := B) i).toRingHom =
      ψ.comp (PiTensorProduct.singleAlgHom (R := R) (A := B) i).toRingHom) : φ = ψ := by
  let : Algebra R T := (φ.comp (algebraMap R _)).toAlgebra
  let φ' : (⨂[R] i, B i) →ₐ[R] T := { φ with commutes' := fun _ ↦ rfl }
  let ψ' : (⨂[R] i, B i) →ₐ[R] T :=
    { ψ with commutes' := fun r ↦ (RingHom.congr_fun hR r).symm }
  have : φ' = ψ' := PiTensorProduct.algHom_ext fun i ↦ AlgHom.ext fun b ↦
    RingHom.congr_fun (h i) b
  exact RingHom.ext fun x ↦ AlgHom.congr_fun this x

end RingHomExt

/-! ### Base change of a finite tensor product -/

section BaseChange

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι]
  [DecidableEq ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- `A ⊗_R ⨂_R B_i → ⨂_A (A ⊗_R B_i)`, `a ⊗ (b_i)_i ↦ a · ⊗_i (1 ⊗ b_i)`. -/
def piTensorBaseChangeHom : A ⊗[R] (⨂[R] i, B i) →ₐ[A] ⨂[A] i, A ⊗[R] B i :=
  Algebra.TensorProduct.lift (Algebra.ofId A _)
    (piLift fun i ↦ ((PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i)
      i).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ ↦ Commute.all _ _

/-- `piTensorBaseChangeHom` on `1 ⊗ b` with `b` in the `i`-th factor. -/
theorem piTensorBaseChangeHom_one_tmul_single (i : ι) (b : B i) :
    piTensorBaseChangeHom R A B ((1 : A) ⊗ₜ[R] PiTensorProduct.singleAlgHom i b) =
      PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i) i (1 ⊗ₜ b) := by
  rw [piTensorBaseChangeHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul, piLift_single]
  rfl

/-- `⨂_A (A ⊗_R B_i) → A ⊗_R ⨂_R B_i`, `a ⊗ b` in the `i`-th factor `↦ a ⊗ b_i`. -/
def piTensorBaseChangeInv : (⨂[A] i, A ⊗[R] B i) →ₐ[A] A ⊗[R] (⨂[R] i, B i) :=
  piLift fun i ↦ Algebra.TensorProduct.map (AlgHom.id A A)
    (PiTensorProduct.singleAlgHom (R := R) (A := B) i)

/-- `piTensorBaseChangeInv` on the `i`-th factor. -/
theorem piTensorBaseChangeInv_single (i : ι) (a : A) (b : B i) :
    piTensorBaseChangeInv R A B (PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i) i
      (a ⊗ₜ b)) = a ⊗ₜ PiTensorProduct.singleAlgHom i b := by
  rw [piTensorBaseChangeInv, piLift_single]
  rfl

/-- **`A ⊗_R ⨂_R B_i ≅ ⨂_A (A ⊗_R B_i)`.** -/
def piTensorBaseChangeEquiv : A ⊗[R] (⨂[R] i, B i) ≃ₐ[A] ⨂[A] i, A ⊗[R] B i :=
  AlgEquiv.ofAlgHom (piTensorBaseChangeHom R A B) (piTensorBaseChangeInv R A B)
    (PiTensorProduct.algHom_ext fun i ↦ Algebra.TensorProduct.ext' fun a b ↦ by
      change piTensorBaseChangeHom R A B (piTensorBaseChangeInv R A B
        (PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i) i (a ⊗ₜ b))) =
        PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i) i (a ⊗ₜ b)
      rw [piTensorBaseChangeInv_single, piTensorBaseChangeHom, Algebra.TensorProduct.lift_tmul,
        piLift_single]
      change algebraMap A _ a * PiTensorProduct.singleAlgHom (R := A)
        (A := fun i ↦ A ⊗[R] B i) i (1 ⊗ₜ b) = _
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← map_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (PiTensorProduct.algHom_ext fun i ↦ AlgHom.ext fun b ↦ by
        change piTensorBaseChangeInv R A B (piTensorBaseChangeHom R A B
          ((1 : A) ⊗ₜ[R] PiTensorProduct.singleAlgHom i b)) = 1 ⊗ₜ PiTensorProduct.singleAlgHom i b
        rw [piTensorBaseChangeHom_one_tmul_single, piTensorBaseChangeInv_single]))

/-- `piTensorBaseChangeEquiv` on `1 ⊗ b` with `b` in the `i`-th factor. -/
theorem piTensorBaseChangeEquiv_one_tmul_single (i : ι) (b : B i) :
    piTensorBaseChangeEquiv R A B ((1 : A) ⊗ₜ[R] PiTensorProduct.singleAlgHom i b) =
      PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ A ⊗[R] B i) i (1 ⊗ₜ b) :=
  piTensorBaseChangeHom_one_tmul_single R A B i b

end BaseChange

/-! ### Base change along a pushout square -/

section IsPushout

variable {A' A R' R : Type*} [CommRing A'] [CommRing A] [CommRing R'] [CommRing R]
  [Algebra A' A] [Algebra A' R'] [Algebra A R] [Algebra R' R] [Algebra A' R]
  [IsScalarTower A' A R] [IsScalarTower A' R' R] [Algebra.IsPushout A' A R' R]
  {M' N : Type*} [AddCommGroup M'] [Module A' M'] [Module R' M'] [IsScalarTower A' R' M']
  [AddCommGroup N] [Module R N] [instR'N : Module R' N] [towR'RN : IsScalarTower R' R N]
  [instAN : Module A N] [towARN : IsScalarTower A R N] [instA'N : Module A' N]
  [towA'R'N : IsScalarTower A' R' N] [towA'AN : IsScalarTower A' A N]

/-- **Base change along one side of a pushout square of rings.**  If `R = A ⊗_{A'} R'` and
`N = R ⊗_{R'} M'`, then `N = A ⊗_{A'} M'`. -/
theorem isBaseChange_restrictScalars_of_isPushout {ρ : M' →ₗ[R'] N} (hρ : IsBaseChange R ρ) :
    IsBaseChange A (ρ.restrictScalars A') := by
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange A' A R' R M').symm.trans (hρ.equiv.restrictScalars A))
    fun x ↦ ?_
  change hρ.equiv ((Algebra.IsPushout.cancelBaseChange A' A R' R M').symm (1 ⊗ₜ x)) = ρ x
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, IsBaseChange.equiv_tmul, one_smul]

end IsPushout

end Crystalline.GlobalCrystallineSituation.CechEnvelope
