module

public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairingTrace
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.LinearCombination

/-!
# The characteristic polynomial of an endomorphism with a twisted adjoint

Let `G` be a free module of finite rank `r` over `ℤ/N`, `e` a left-nondegenerate pairing on `G`
with values in `ℤ/N`, `σ, τ` endomorphisms with `e(σa, σb) = c e(a, b)`, `στ = τσ = c`, `c` a
unit. Then `τ` is the adjoint of `σ`, so the two have the same characteristic polynomial `P`,
and `τ = c σ⁻¹` gives `P(0) P = X^r P(c/X)`: `P(0) · P_j = c^{r-j} P_{r-j}` for all `j ≤ r`.
For the Frobenius on the `ℓⁿ`-torsion of the Picard group of a curve this is the symmetry
`b ↦ q/b` of the eigenvalues, from the Weil pairing.

## Main results

* `Stacks.Picard.charpoly_eq_of_pairing`: `P_σ = P_τ`.
* `Stacks.Picard.charpoly_coeff_zero_mul_coeff_eq_of_pairing`: `P(0) P_j = c^{r-j} P_{r-j}`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.Picard

section Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `det(c - X M) = c^r · charpolyRev(M)(X / c)` for a unit `c`. -/
theorem det_C_sub_X_smul_eq (M : Matrix ι ι R) (c : Rˣ) :
    (Matrix.scalar ι (C (c : R)) - (X : R[X]) • M.map C).det =
      C ((c : R) ^ Fintype.card ι) * M.charpolyRev.comp (C (c⁻¹ : Rˣ).1 * X) := by
  have h1 : Matrix.scalar ι (C (c : R)) - (X : R[X]) • M.map C =
      C (c : R) • (1 - (C (c⁻¹ : Rˣ).1 * X) • M.map C) := by
    rw [smul_sub, smul_smul, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h1, Matrix.det_smul, Matrix.charpolyRev, ← C_pow]
  congr 1
  have h2 : (1 - (C (c⁻¹ : Rˣ).1 * X) • M.map C) =
      (compRingHom (C (c⁻¹ : Rˣ).1 * X)).mapMatrix (1 - (X : R[X]) • M.map C) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [hij] <;> ring
  rw [h2, ← RingHom.map_det]
  rfl

/-- The `j`-th coefficient of `P(a X)` is `a ^ j` times the `j`-th coefficient of `P`. -/
theorem coeff_comp_C_mul_X (P : R[X]) (a : R) (j : ℕ) :
    (P.comp (C a * X)).coeff j = a ^ j * P.coeff j := by
  rw [comp, eval₂_eq_sum_range, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, mul_comm]
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb)]
  · intro hj
    rw [Finset.mem_range, not_lt] at hj
    rw [ite_eq_left rfl, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- `det M · charpoly N = (-1)^r det(c - X M)` when `M N = c`. -/
private theorem C_det_mul_charpoly_eq_of_mul_eq (M N : Matrix ι ι R) (c : Rˣ)
    (hMN : M * N = Matrix.scalar ι (c : R)) :
    C M.det * N.charpoly =
      (-1) ^ Fintype.card ι * (Matrix.scalar ι (C (c : R)) - (X : R[X]) • M.map C).det := by
  have e1 : (C : R →+* R[X]).mapMatrix M * Matrix.scalar ι (X : R[X]) =
      (X : R[X]) • M.map (C : R →+* R[X]) := by
    rw [Matrix.scalar_apply]
    refine Matrix.ext fun i k => ?_
    rw [Matrix.mul_diagonal, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact mul_comm _ _
  have e2 : (C : R →+* R[X]).mapMatrix M * (C : R →+* R[X]).mapMatrix N =
      Matrix.scalar ι (C (c : R)) := by
    rw [← map_mul ((C : R →+* R[X]).mapMatrix (m := ι)), hMN]
    simp [Matrix.scalar_apply]
  rw [Matrix.charpoly, Matrix.charmatrix, RingHom.map_det, ← Matrix.det_mul, mul_sub, e1, e2,
    ← neg_sub, Matrix.det_neg]

/-- **The coefficient identity for `M N = N M = c` and equal characteristic polynomials.** -/
theorem charpoly_coeff_symm_of_mul_eq (M N : Matrix ι ι R) (c : Rˣ)
    (hMN : M * N = Matrix.scalar ι (c : R)) (hchar : N.charpoly = M.charpoly) (j : ℕ)
    (hj : j ≤ Fintype.card ι) :
    M.charpoly.coeff 0 * M.charpoly.coeff j =
      (c : R) ^ (Fintype.card ι - j) * M.charpoly.coeff (Fintype.card ι - j) := by
  nontriviality R
  have key := C_det_mul_charpoly_eq_of_mul_eq M N c hMN
  set r := Fintype.card ι
  rw [hchar, det_C_sub_X_smul_eq, Matrix.det_eq_sign_charpoly_coeff M] at key
  have hc := congrArg (fun P : R[X] => P.coeff j) key
  rw [show ((-1 : R[X]) ^ r) = C ((-1) ^ r) by simp, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_comp_C_mul_X, ← Matrix.reverse_charpoly, coeff_reverse,
    Matrix.charpoly_natDegree_eq_dim, revAt_le hj] at hc
  have hu2 : (c : R) ^ r * ((c⁻¹ : Rˣ) : R) ^ j = (c : R) ^ (r - j) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val]
    congr 1
    rw [inv_pow, show r = (r - j) + j by omega, pow_add, mul_inv_cancel_right]
    simp
  have hsq : ((-1 : R) ^ r) * ((-1) ^ r) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  linear_combination ((-1 : R) ^ r) * hc + ((-1 : R) ^ r * (-1) ^ r *
    M.charpoly.coeff (r - j)) * hu2 + ((c : R) ^ (r - j) * M.charpoly.coeff (r - j) -
    M.charpoly.coeff 0 * M.charpoly.coeff j) * hsq

end Matrix

section Pairing

variable {N : ℕ} [NeZero N] {G : Type*} [AddCommGroup G] [Module (ZMod N) G]
  [Module.Free (ZMod N) G] [Module.Finite (ZMod N) G]

/-- **An endomorphism and its adjoint for a nondegenerate pairing have the same characteristic
polynomial.** -/
theorem charpoly_eq_of_pairing (σ τ : G →ₗ[ZMod N] G) (c : ZMod N) (hc : IsUnit c)
    (e : G →+ G →+ ZMod N) (he : ∀ a, (∀ b, e a b = 0) → a = 0)
    (hσ : ∀ a b, e (σ a) (σ b) = c * e a b) (hστ : ∀ a, σ (τ a) = c • a) :
    σ.charpoly = τ.charpoly := by
  classical
  rcases subsingleton_or_nontrivial (ZMod N) with hN | hN
  · exact Subsingleton.elim _ _
  have hlin : ∀ (a : G) (t : ZMod N) (b : G), e a (t • b) = t * e a b := fun a t b =>
    ((e a).toZModLinearMap N).map_smul t b
  have hlin' : ∀ (t : ZMod N) (a b : G), e (t • a) b = t * e a b := fun t a b =>
    congrArg (fun f : G →+ ZMod N => f b) ((e.toZModLinearMap N).map_smul t a)
  let Φ : G →ₗ[ZMod N] Module.Dual (ZMod N) G :=
    { toFun := fun a => (e a).toZModLinearMap N
      map_add' := fun a a' => LinearMap.ext fun b => by simp
      map_smul' := fun t a => LinearMap.ext fun b => by simp [hlin'] }
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun a ha => he a fun b => congrArg (fun f : Module.Dual (ZMod N) G => f b) ha
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := ZMod N) (M := G)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : Finite G := Module.finite_of_finite (ZMod N)
  have : Finite (Module.Dual (ZMod N) G) := Finite.of_equiv _ b.dualBasis.equivFun.toEquiv.symm
  have hΦbij : Function.Bijective Φ := hΦinj.bijective_of_nat_card_le
    (Nat.card_congr (b.dualBasis.equivFun.toEquiv.trans b.equivFun.toEquiv.symm)).le
  let Φe := LinearEquiv.ofBijective Φ hΦbij
  have hadj : ∀ a b, e (σ a) b = e a (τ b) := fun a b => by
    obtain ⟨u, rfl⟩ := hc
    have h := hσ a (τ b)
    rw [hστ, hlin] at h
    exact (Units.mul_right_inj u).1 h
  have hconj : Φe.conj σ = Module.Dual.transpose τ := by
    refine LinearMap.ext fun f => LinearMap.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hΦbij.2 f
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show Φe.symm (Φ a) = a from Φe.symm_apply_apply a]
    exact hadj a b
  rw [← LinearEquiv.charpoly_conj Φe σ, hconj, ← LinearMap.charpoly_toMatrix _ b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

/-- **The symmetry of the characteristic polynomial from a twisted pairing**: with
`e(σa, σb) = c e(a, b)` and `στ = τσ = c`, the characteristic polynomial `P` of `σ` on `G`
(free of rank `r`) satisfies `P(0) P_j = c^{r-j} P_{r-j}` for `j ≤ r`. -/
theorem charpoly_coeff_zero_mul_coeff_eq_of_pairing (σ τ : G →ₗ[ZMod N] G) (c : ZMod N)
    (hc : IsUnit c) (e : G →+ G →+ ZMod N) (he : ∀ a, (∀ b, e a b = 0) → a = 0)
    (hσ : ∀ a b, e (σ a) (σ b) = c * e a b) (hστ : ∀ a, σ (τ a) = c • a)
    (hτσ : ∀ a, τ (σ a) = c • a) (j : ℕ) (hj : j ≤ Module.finrank (ZMod N) G) :
    σ.charpoly.coeff 0 * σ.charpoly.coeff j =
      c ^ (Module.finrank (ZMod N) G - j) *
        σ.charpoly.coeff (Module.finrank (ZMod N) G - j) := by
  classical
  rcases subsingleton_or_nontrivial (ZMod N) with hN | hN
  · exact Subsingleton.elim _ _
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := ZMod N) (M := G)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have hr : Module.finrank (ZMod N) G = Fintype.card ι := Module.finrank_eq_card_basis b
  obtain ⟨u, rfl⟩ := hc
  have hMN : LinearMap.toMatrix b b σ * LinearMap.toMatrix b b τ =
      Matrix.scalar ι (u : ZMod N) := by
    rw [← LinearMap.toMatrix_mul,
      show σ * τ = (u : ZMod N) • LinearMap.id from LinearMap.ext hστ, map_smul,
      LinearMap.toMatrix_id, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hchar : (LinearMap.toMatrix b b τ).charpoly = (LinearMap.toMatrix b b σ).charpoly := by
    rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
      charpoly_eq_of_pairing σ τ u u.isUnit e he hσ hστ]
  rw [hr]
  simpa only [LinearMap.charpoly_toMatrix] using
    charpoly_coeff_symm_of_mul_eq _ _ u hMN hchar j (hr ▸ hj)

end Pairing

end Stacks.Picard
