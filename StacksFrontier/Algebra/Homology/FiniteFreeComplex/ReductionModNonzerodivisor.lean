module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reduction of an exact complex modulo a nonzerodivisor

This file proves that exactness of a complex of finite free modules over a local ring is preserved,
except at `R^{n_1}`, by reduction modulo a nonzerodivisor in the maximal ideal (Stacks, Tag 00MZ).
-/

@[expose] public section

open LinearMap Submodule Matrix

variable {R : Type*} [CommRing R]

/-- The complex condition `φ i * φ (i+1) = 0` for a family of matrices representing differentials
`φ i : R^{n (i+1)} → R^{n i}`. -/
def IsMatrixComplex (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R) : Prop :=
  ∀ i, (φ i) * (φ (i + 1)) = 0

/-- Exactness at the module `R^{n (i+1)}` in position `i+1`:
`ker (φ i).mulVecLin = range (φ (i+1)).mulVecLin`. -/
def ExactAtSucc (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R) (i : ℕ) : Prop :=
  LinearMap.ker (φ i).mulVecLin = LinearMap.range (φ (i + 1)).mulVecLin

/-- Reduction modulo `x`: each matrix reduced entrywise along the quotient map `R → R/xR`. -/
def reduceMat (x : R) (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (i : ℕ) : Matrix (Fin (n i)) (Fin (n (i + 1))) (R ⧸ Ideal.span {x}) :=
  (φ i).map (Ideal.Quotient.mk (Ideal.span {x}))

/-- Multiplying a vector by `x` entrywise commutes with matrix-vector multiplication. -/
private theorem mulVec_const_mul {p q : ℕ} (x : R) (M : Matrix (Fin p) (Fin q) R) (u : Fin q → R) :
    M *ᵥ (fun a => x * u a) = fun b => x * (M *ᵥ u) b :=
  Matrix.mulVec_smul M x u

/-- The reduction of a product of matrices with zero product has zero product. -/
private theorem reduceMat_mul_eq_zero (x : R) (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R) {i : ℕ}
    (h : φ i * φ (i + 1) = 0) :
    reduceMat x n φ i * reduceMat x n φ (i + 1) = 0 := by
  change (φ i).map _ * (φ (i + 1)).map _ = 0
  rw [← Matrix.map_mul, h]
  simp

/-- Let `R` be a commutative local ring with maximal ideal `m`, and let
`φ : R^{n (•+1)} → R^{n •}` be a complex of finite free modules ending at position
`e` (so `n (e+1) = 0`).  If the complex is exact at positions `1, ..., e` and
`x ∈ m` is a nonzerodivisor of `R`, then the reduced complex `φ mod x` is exact at
positions `2, ..., e`. -/
@[stacks 00MZ]
theorem tag_00MZ (R : Type*) [CommRing R] [IsLocalRing R]
    (e : ℕ) (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (hcomplex : IsMatrixComplex n φ)
    (x : R)
    (hxnzd : ∀ r : R, x * r = 0 → r = 0)
    (hexact : ∀ i, i < e → ExactAtSucc n φ i) :
    ∀ i, 1 ≤ i → i < e → ExactAtSucc n (reduceMat x n φ) i := by
  set mk := Ideal.Quotient.mk (Ideal.span {x}) with hmk
  have map_mulVec : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) R) (v : Fin q → R),
      (M.map mk).mulVec (fun a => mk (v a)) = fun b => mk (M.mulVec v b) := by
    intro p q M v
    ext b
    simp [Matrix.mulVec, Matrix.map, dotProduct, map_sum, map_mul]
  have lift : ∀ {q : ℕ} (w : Fin q → R ⧸ Ideal.span {x}),
      ∃ v : Fin q → R, (fun a => mk (v a)) = w := by
    intro q w
    choose v hv using fun a => Ideal.Quotient.mk_surjective (w a)
    exact ⟨v, funext hv⟩
  have vanish : ∀ {q : ℕ} (v : Fin q → R), (fun a => mk (v a)) = 0 →
      ∃ u : Fin q → R, v = fun a => x * u a := by
    intro q v hv
    have hcomp : ∀ a, mk (v a) = 0 := fun a => congrFun hv a
    have hex : ∀ a, ∃ c, v a = x * c := by
      intro a
      have h2 : v a ∈ Ideal.span {x} := (Ideal.Quotient.eq_zero_iff_mem).mp (hcomp a)
      rw [Ideal.mem_span_singleton'] at h2
      obtain ⟨c, hc⟩ := h2
      exact ⟨c, by rw [← hc]; ring⟩
    choose u hu using hex
    exact ⟨u, funext hu⟩
  have nzd_vec : ∀ {q : ℕ} (v : Fin q → R), (fun a => x * v a) = 0 → v = 0 := by
    intro q v hv
    funext a
    exact hxnzd (v a) (congrFun hv a)
  intro i hi1 hie
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hexj : ExactAtSucc n φ j := hexact j (by omega)
  have hexj1 : ExactAtSucc n φ (j + 1) := hexact (j + 1) hie
  apply le_antisymm
  · rintro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨v, rfl⟩ := lift w
    rw [Matrix.mulVecLin_apply] at hw
    show _ ∈ LinearMap.range ((reduceMat x n φ (j + 1 + 1)).mulVecLin)
    have hwc : (fun b => mk ((φ (j + 1) *ᵥ v) b)) = 0 := by
      rw [show reduceMat x n φ (j + 1) = (φ (j + 1)).map mk from rfl] at hw
      rw [map_mulVec (φ (j + 1)) v] at hw
      exact hw
    obtain ⟨w0, hw0⟩ := vanish (φ (j + 1) *ᵥ v) hwc
    have hcomp : φ j *ᵥ (φ (j + 1) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hcomplex j]
      simp
    rw [hw0] at hcomp
    rw [mulVec_const_mul] at hcomp
    have hjw0 : (φ j *ᵥ w0) = 0 := nzd_vec (φ j *ᵥ w0) hcomp
    have hw0mem : w0 ∈ LinearMap.range ((φ (j + 1)).mulVecLin) := by
      rw [← hexj, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hjw0
    rw [LinearMap.mem_range] at hw0mem
    obtain ⟨u, hu⟩ := hw0mem
    rw [Matrix.mulVecLin_apply] at hu
    have hkey : φ (j + 1) *ᵥ (v - fun a => x * u a) = 0 := by
      rw [Matrix.mulVec_sub, hw0]
      rw [mulVec_const_mul, hu]
      simp
    have hmem : (v - fun a => x * u a) ∈ LinearMap.range ((φ (j + 1 + 1)).mulVecLin) := by
      rw [← hexj1, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hkey
    rw [LinearMap.mem_range] at hmem
    obtain ⟨t, ht⟩ := hmem
    rw [Matrix.mulVecLin_apply] at ht
    rw [LinearMap.mem_range]
    refine ⟨(fun a => mk (t a)), ?_⟩
    rw [Matrix.mulVecLin_apply]
    show (reduceMat x n φ (j + 1 + 1)).mulVec (fun a => mk (t a)) = _
    rw [show reduceMat x n φ (j + 1 + 1) = (φ (j + 1 + 1)).map mk from rfl]
    rw [map_mulVec (φ (j + 1 + 1)) t, ht]
    funext a
    show mk ((v - fun a => x * u a) a) = mk (v a)
    simp only [Pi.sub_apply]
    rw [map_sub]
    have : mk (x * u a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨u a, rfl⟩
    rw [this, sub_zero]
  · rw [LinearMap.range_le_ker_iff]
    show (reduceMat x n φ (j + 1)).mulVecLin ∘ₗ (reduceMat x n φ (j + 1 + 1)).mulVecLin = 0
    rw [← Matrix.mulVecLin_mul]
    rw [reduceMat_mul_eq_zero x n φ (hcomplex (j + 1)), Matrix.mulVecLin_zero]

/-- Reducing a complex of matrices modulo `x` gives again a complex. -/
theorem reduceMat_isComplex (x : R) (n : ℕ → ℕ)
    (φ : (i : ℕ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (h : IsMatrixComplex n φ) :
    IsMatrixComplex n (reduceMat x n φ) := by
  exact fun i => reduceMat_mul_eq_zero x n φ (h i)

end
