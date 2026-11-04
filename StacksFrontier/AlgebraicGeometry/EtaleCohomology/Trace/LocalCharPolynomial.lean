module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionEulerProduct

/-!
# The local factor as a polynomial, and base change of the coefficient ring

The local factor `det(1 - A ⬝ T ^ d)` of a square matrix `A` over `Λ` is a polynomial: the
determinant of a matrix whose entries are polynomials of degree at most `d`. This module records it
as such, `localCharPolynomial`, together with the facts that its image in `Λ⟦T⟧` is
`localCharSeries`, that its constant coefficient is `1`, and that its degree is at most `d * rank`.

The second half is base change. A ring homomorphism `φ : Λ → Λ'` carries the local factor of `A` to
the local factor of `A.map φ`, hence the local Euler factor to the local Euler factor, and
therefore the whole L-function of a family of Frobenius matrices to the L-function of the
base-changed family.

## Main definitions

* `Stacks.EtaleCohomology.localCharPolynomial`: the local factor `det(1 - A ⬝ T ^ d)` as an
  element of `Λ[T]`.
* `Stacks.EtaleCohomology.FrobeniusMatrices.map`: a family of Frobenius matrices with its
  coefficient ring changed along a ring homomorphism.

## Main results

* `Stacks.EtaleCohomology.coe_localCharPolynomial`: the polynomial local factor becomes
  `localCharSeries` in `Λ⟦T⟧`.
* `Stacks.EtaleCohomology.natDegree_localCharPolynomial_le` and
  `Stacks.EtaleCohomology.coeff_zero_localCharPolynomial`: its degree and constant coefficient.
* `Stacks.EtaleCohomology.map_localCharSeries_eq` and
  `Stacks.EtaleCohomology.map_localEulerFactor`: base change of the local factors.
* `Stacks.EtaleCohomology.FrobeniusMatrices.map_lFunction`: base change of the L-function.

## References

* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The local factor as a polynomial -/

section Polynomial

variable {Λ : Type v} [CommRing Λ] {n : Type w} [Fintype n] [DecidableEq n]

/-- The matrix `1 - T ^ d • A` over the polynomial ring `Λ[T]`. -/
public def localCharPolyMatrix (A : Matrix n n Λ) (d : ℕ) : Matrix n n (Polynomial Λ) :=
  1 - (Polynomial.X : Polynomial Λ) ^ d • A.map Polynomial.C

/-- The local factor `det(1 - A ⬝ T ^ d)` of a square matrix `A` over `Λ` at a point of degree
`d`, as a polynomial. Its image in `Λ⟦T⟧` is `localCharSeries A d`. -/
public def localCharPolynomial (A : Matrix n n Λ) (d : ℕ) : Polynomial Λ :=
  (localCharPolyMatrix A d).det

omit [Fintype n] in
/-- The `(i, j)` entry of `1 - T ^ d • A` is `(if i = j then 1 else 0) - T ^ d * A i j`. -/
public theorem localCharPolyMatrix_apply (A : Matrix n n Λ) (d : ℕ) (i j : n) :
    localCharPolyMatrix A d i j =
      (if i = j then 1 else 0) - Polynomial.X ^ d * Polynomial.C (A i j) := by
  simp [localCharPolyMatrix, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- The polynomial local factor maps to the power series local factor. -/
public theorem coe_localCharPolynomial (A : Matrix n n Λ) (d : ℕ) :
    (localCharPolynomial A d : Λ⟦X⟧) = localCharSeries A d := by
  have hm : (Polynomial.coeToPowerSeries.ringHom (R := Λ)).mapMatrix (localCharPolyMatrix A d)
      = localCharMatrix A d := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, localCharPolyMatrix_apply,
      Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [localCharMatrix, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
    split_ifs <;>
      simp [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]
  rw [localCharSeries, ← hm, ← RingHom.map_det, localCharPolynomial,
    Polynomial.coeToPowerSeries.ringHom_apply]

/-- The polynomial local factor at a point of nonzero degree has constant coefficient `1`. -/
public theorem coeff_zero_localCharPolynomial (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    (localCharPolynomial A d).coeff 0 = 1 := by
  have h := constantCoeff_localCharSeries A hd (n := n)
  rwa [← coe_localCharPolynomial, Polynomial.constantCoeff_coe] at h

omit [Fintype n] in
/-- Every entry of `1 - T ^ d • A` has degree at most `d`. -/
private lemma natDegree_localCharPolyMatrix_apply_le (A : Matrix n n Λ) (d : ℕ) (i j : n) :
    (localCharPolyMatrix A d i j).natDegree ≤ d := by
  rw [localCharPolyMatrix_apply]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · split_ifs <;> simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simpa using le_trans Polynomial.natDegree_pow_le
      (by simpa using Nat.mul_le_mul_left d Polynomial.natDegree_X_le)

/-- The polynomial local factor has degree at most `d` times the rank. -/
public theorem natDegree_localCharPolynomial_le (A : Matrix n n Λ) (d : ℕ) :
    (localCharPolynomial A d).natDegree ≤ d * Fintype.card n := by
  rw [localCharPolynomial, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ i, (localCharPolyMatrix A d (σ i) i).natDegree
      ≤ ∑ _i : n, d :=
        Finset.sum_le_sum fun i _ => natDegree_localCharPolyMatrix_apply_le A d (σ i) i
    _ = d * Fintype.card n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end Polynomial

/-! ### The local factor of a scalar -/

section Scalar

variable {Λ : Type v} [CommRing Λ]

/-- The local factor of the `1 × 1` matrix `a` at a point of degree `d` is `1 - a T ^ d`. -/
public theorem localCharSeries_diagonal_fin_one (a : Λ) (d : ℕ) :
    localCharSeries (Matrix.diagonal fun _ : Fin 1 => a) d
      = 1 - PowerSeries.C a * PowerSeries.X ^ d := by
  rw [localCharSeries, Matrix.det_fin_one]
  simp only [localCharMatrix, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
    Matrix.map_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
  ring

/-- The local factor of the `1 × 1` identity matrix at a point of degree `d` is `1 - T ^ d`. -/
public theorem localCharSeries_one_fin_one (d : ℕ) :
    localCharSeries (1 : Matrix (Fin 1) (Fin 1) Λ) d = 1 - (PowerSeries.X : Λ⟦X⟧) ^ d := by
  have h : (1 : Matrix (Fin 1) (Fin 1) Λ) = Matrix.diagonal fun _ : Fin 1 => (1 : Λ) := by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [h, localCharSeries_diagonal_fin_one]
  simp

end Scalar

/-! ### Base change of the coefficient ring -/

section BaseChange

variable {Λ : Type v} [CommRing Λ] {Λ' : Type*} [CommRing Λ'] {n : Type w} [Fintype n]
  [DecidableEq n]

/-- The local factor commutes with base change of the coefficient ring. -/
public theorem map_localCharSeries_eq (φ : Λ →+* Λ') (A : Matrix n n Λ) (d : ℕ) :
    PowerSeries.map φ (localCharSeries A d) = localCharSeries (A.map φ) d := by
  have hm : (PowerSeries.map φ).mapMatrix (localCharMatrix A d) = localCharMatrix (A.map φ) d := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [localCharMatrix, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [localCharSeries, RingHom.map_det, hm, localCharSeries]

/-- The local Euler factor commutes with base change of the coefficient ring. -/
public theorem map_localEulerFactor (φ : Λ →+* Λ') (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.map φ (localEulerFactor A d) = localEulerFactor (A.map φ) d := by
  have h1 : localCharSeries (A.map φ) d * PowerSeries.map φ (localEulerFactor A d) = 1 := by
    rw [← map_localCharSeries_eq, ← map_mul, localCharSeries_mul_localEulerFactor A hd, map_one]
  have h2 := localCharSeries_mul_localEulerFactor (A.map φ) hd
  calc PowerSeries.map φ (localEulerFactor A d)
      = localCharSeries (A.map φ) d * localEulerFactor (A.map φ) d *
          PowerSeries.map φ (localEulerFactor A d) := by rw [h2, one_mul]
    _ = localEulerFactor (A.map φ) d *
          (localCharSeries (A.map φ) d * PowerSeries.map φ (localEulerFactor A d)) := by ring
    _ = localEulerFactor (A.map φ) d := by rw [h1, mul_one]

namespace FrobeniusMatrices

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}

/-- A family of Frobenius matrices with its coefficient ring changed along a ring
homomorphism. -/
public def map (φ : Λ →+* Λ') (D : FrobeniusMatrices f Λ) : FrobeniusMatrices f Λ' where
  rank := D.rank
  matrix x := (D.matrix x).map φ

/-- Changing the coefficient ring does not change the rank. -/
public theorem rank_map (φ : Λ →+* Λ') (D : FrobeniusMatrices f Λ) : (D.map φ).rank = D.rank :=
  rfl

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

omit [Finite k] [QuasiCompact f] in
/-- The local Euler factors of a base-changed family are the base-changed local Euler
factors. -/
public theorem localFactor_map (φ : Λ →+* Λ') (D : FrobeniusMatrices f Λ)
    (x : closedPoints X) :
    (D.map φ).localFactor x = PowerSeries.map φ (D.localFactor x) :=
  (map_localEulerFactor φ (D.matrix x) (residueDegree_pos f x.1 x.2).ne').symm

/-- The L-function commutes with base change of the coefficient ring. -/
public theorem map_lFunction (φ : Λ →+* Λ') (D : FrobeniusMatrices f Λ) :
    PowerSeries.map φ D.lFunction = (D.map φ).lFunction := by
  ext m
  rw [PowerSeries.coeff_map, D.coeff_lFunction, (D.map φ).coeff_lFunction,
    show (D.map φ).eulerSystem.support m = D.eulerSystem.support m from rfl,
    ← PowerSeries.coeff_map]
  refine congrArg _ ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun x _ => (localFactor_map φ D x).symm

end FrobeniusMatrices

end BaseChange

end Stacks.EtaleCohomology

end
