module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionEulerProduct
public import StacksFrontier.RingTheory.Derivation.Determinant
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative

/-!
# The logarithmic derivative of a local factor

The local factor `det(1 - A ⬝ T ^ d)` of a square matrix `A` over a commutative ring `Λ` at a
point of degree `d` satisfies

`T d/dT log det(1 - A ⬝ T ^ d) ⁻¹ = d · ∑_{m ≥ 1} tr(A ^ m) T ^ (m d)`,

the identity that converts an Euler product of local factors into a sum of traces of powers of
Frobenius.  Over `Λ⟦T⟧` the matrix `1 - A ⬝ T ^ d` is invertible with inverse the geometric
series `∑_{m ≥ 0} A ^ m T ^ (m d)`, so its adjugate is the determinant times that series;
Jacobi's formula then turns the derivative of the determinant into the trace of the geometric
series against `A`, whose coefficients are the traces of the powers of `A`.

## Main definitions

* `Stacks.EtaleCohomology.geomSeriesMatrix`: the geometric series `∑_{m ≥ 0} A ^ m T ^ (m d)`,
  the inverse of `1 - A ⬝ T ^ d` over `Λ⟦T⟧`.
* `Stacks.EtaleCohomology.traceSeries`: the series `∑_{m ≥ 1} tr(A ^ m) T ^ (m d)`.

## Main results

* `Stacks.EtaleCohomology.geomSeriesMatrix_mul_localCharMatrix`: the geometric series inverts
  `1 - A ⬝ T ^ d`.
* `Stacks.EtaleCohomology.logDerivative_localCharSeries` and
  `Stacks.EtaleCohomology.logDerivative_localEulerFactor`: the logarithmic derivative of the
  local factor and of its inverse.

## References

* [Stacks Project, Tag 03UY](https://stacks.math.columbia.edu/tag/03UY), where this identity
  is the "formula which holds for any commutative ring and any endomorphism of a finite
  projective module".
-/

@[expose] public noncomputable section

open Finset Matrix PowerSeries

universe v w

namespace Stacks.EtaleCohomology

variable {Λ : Type v} [CommRing Λ] {n : Type w} [Fintype n] [DecidableEq n]

/-! ### Two arithmetic identities between conditional sums -/

omit [Fintype n] [DecidableEq n] in
/-- Reindexing a sum supported in the degrees divisible by `d`: the value in degree `m` of a
series shifted by `T ^ d` is the value of the unshifted series, which is nonzero only when `d`
divides `m` and `m` is positive. -/
private lemma ite_le_eq (f : ℕ → Λ) {d : ℕ} (hd : d ≠ 0) (m : ℕ) :
    (if d ≤ m then (if d ∣ m - d then f ((m - d) / d + 1) else 0) else 0)
      = if d ∣ m ∧ m ≠ 0 then f (m / d) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [show ¬ d ≤ 0 by omega]
  · have hm0 : m ≠ 0 := hm.ne'
    by_cases h1 : d ∣ m
    · have h2 : d ≤ m := Nat.le_of_dvd hm h1
      have h3 : d ∣ m - d := Nat.dvd_sub h1 dvd_rfl
      rw [Nat.div_eq_sub_div (Nat.pos_of_ne_zero hd) h2]
      simp [h1, h2, h3, hm0]
    · have h3 : ¬ d ∣ m - d ∨ ¬ d ≤ m := by
        by_cases h2 : d ≤ m
        · refine Or.inl fun h3 => h1 ?_
          have hmm : m = m - d + d := by omega
          rw [hmm]
          exact Nat.dvd_add h3 dvd_rfl
        · exact Or.inr h2
      rcases h3 with h3 | h3 <;> simp [h1, h3, hm0]

omit [Fintype n] [DecidableEq n] in
/-- Removing the positivity condition from a sum supported in the degrees divisible by `d`
leaves only the contribution of degree zero. -/
private lemma sub_ite_eq (f : ℕ → Λ) (d m : ℕ) :
    (if d ∣ m then f (m / d) else 0) - (if d ∣ m ∧ m ≠ 0 then f (m / d) else 0)
      = if m = 0 then f 0 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · by_cases hdm : d ∣ m <;> simp [hm, hdm]

/-! ### The geometric series inverse of `1 - A ⬝ T ^ d` -/

/-- The geometric series `∑_{m ≥ 0} A ^ m T ^ (m d)`, as a matrix over `Λ⟦T⟧`.  For `d ≠ 0` it
is the inverse of `1 - A ⬝ T ^ d`. -/
public def geomSeriesMatrix (A : Matrix n n Λ) (d : ℕ) : Matrix n n Λ⟦X⟧ :=
  fun i j => PowerSeries.mk fun m => if d ∣ m then (A ^ (m / d)) i j else 0

/-- The series `∑_{m ≥ 1} tr(A ^ m) T ^ (m d)` of traces of the powers of `A`, placed in the
degrees divisible by `d`. -/
public def traceSeries (A : Matrix n n Λ) (d : ℕ) : Λ⟦X⟧ :=
  PowerSeries.mk fun m => if d ∣ m ∧ m ≠ 0 then (A ^ (m / d)).trace else 0

/-- The coefficients of the trace series. -/
public theorem coeff_traceSeries (A : Matrix n n Λ) (d m : ℕ) :
    coeff m (traceSeries A d) = if d ∣ m ∧ m ≠ 0 then (A ^ (m / d)).trace else 0 :=
  coeff_mk m _

/-- The coefficients of an entry of the geometric series. -/
private lemma coeff_geomSeriesMatrix (A : Matrix n n Λ) (d : ℕ) (i j : n) (m : ℕ) :
    coeff m (geomSeriesMatrix A d i j) = if d ∣ m then (A ^ (m / d)) i j else 0 :=
  coeff_mk m _

/-- Multiplying the geometric series by `A` on the right raises the exponent of every power
of `A` by one. -/
private lemma coeff_sum_geomSeriesMatrix_mul_C (A : Matrix n n Λ) (d : ℕ) (i j : n) (m : ℕ) :
    coeff m (∑ k, geomSeriesMatrix A d i k * PowerSeries.C (A k j))
      = if d ∣ m then (A ^ (m / d + 1)) i j else 0 := by
  simp only [map_sum, coeff_geomSeriesMatrix, PowerSeries.coeff_mul_C, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs with h
  · rw [pow_succ]
    simp [Matrix.mul_apply]
  · rfl

omit [Fintype n] in
/-- The entries of `1 - A ⬝ T ^ d`. -/
private lemma localCharMatrix_apply (A : Matrix n n Λ) (d : ℕ) (i j : n) :
    localCharMatrix A d i j
      = PowerSeries.C ((1 : Matrix n n Λ) i j) - PowerSeries.X ^ d * PowerSeries.C (A i j) := by
  simp [localCharMatrix, Matrix.one_apply, Matrix.sub_apply, apply_ite]

/-- Over `Λ⟦T⟧` the matrix `1 - A ⬝ T ^ d` is inverted by the geometric series. -/
public theorem geomSeriesMatrix_mul_localCharMatrix (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    geomSeriesMatrix A d * localCharMatrix A d = 1 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  have hc : ∀ k, geomSeriesMatrix A d i k * localCharMatrix A d k j
      = geomSeriesMatrix A d i k * PowerSeries.C ((1 : Matrix n n Λ) k j)
        - PowerSeries.X ^ d * (geomSeriesMatrix A d i k * PowerSeries.C (A k j)) := by
    intro k
    rw [localCharMatrix_apply]
    ring
  have h1 : ∑ k, geomSeriesMatrix A d i k * PowerSeries.C ((1 : Matrix n n Λ) k j)
      = geomSeriesMatrix A d i j := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Matrix.one_apply_ne hk])
      (by simp)]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
  apply PowerSeries.ext
  intro m
  have hone : coeff m ((1 : Matrix n n Λ⟦X⟧) i j)
      = if i = j then (if m = 0 then (1 : Λ) else 0) else 0 := by
    rw [Matrix.one_apply]
    split_ifs with h1 h2 <;> simp_all
  rw [map_sub, PowerSeries.coeff_X_pow_mul', coeff_sum_geomSeriesMatrix_mul_C,
    coeff_geomSeriesMatrix, hone, ite_le_eq (fun t => (A ^ t) i j) hd,
    sub_ite_eq (fun t => (A ^ t) i j) d m]
  simp only [pow_zero, Matrix.one_apply]
  split_ifs with h1 h2 h2 <;> simp_all

/-- The adjugate of `1 - A ⬝ T ^ d` is its determinant times the geometric series. -/
public theorem adjugate_localCharMatrix (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    (localCharMatrix A d).adjugate = localCharSeries A d • geomSeriesMatrix A d := by
  have h2 : localCharMatrix A d * geomSeriesMatrix A d = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq n n Λ⟦X⟧ rfl).mp (geomSeriesMatrix_mul_localCharMatrix A hd)
  calc (localCharMatrix A d).adjugate
      = (localCharMatrix A d).adjugate * (localCharMatrix A d * geomSeriesMatrix A d) := by
        rw [h2, Matrix.mul_one]
    _ = (localCharMatrix A d).adjugate * localCharMatrix A d * geomSeriesMatrix A d := by
        rw [Matrix.mul_assoc]
    _ = localCharSeries A d • (1 : Matrix n n Λ⟦X⟧) * geomSeriesMatrix A d := by
        rw [Matrix.adjugate_mul, localCharSeries]
    _ = localCharSeries A d • geomSeriesMatrix A d := by rw [Matrix.smul_mul, Matrix.one_mul]

omit [Fintype n] in
/-- The entrywise derivative of `1 - A ⬝ T ^ d`. -/
public theorem map_derivative_localCharMatrix (A : Matrix n n Λ) (d : ℕ) :
    (localCharMatrix A d).map (d⁄dX Λ)
      = -(((d : ℕ) : Λ⟦X⟧) * PowerSeries.X ^ (d - 1)) • A.map PowerSeries.C := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, localCharMatrix_apply, map_sub, derivative_C, Derivation.leibniz,
    derivative_pow, derivative_X, derivative_C]
  simp only [smul_eq_mul, Matrix.smul_apply, Matrix.map_apply]
  ring

/-- The trace of the geometric series against `A`, multiplied by `T ^ d`, is the series of
traces of the powers of `A`. -/
public theorem X_pow_mul_trace_geomSeriesMatrix (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.X ^ d * (geomSeriesMatrix A d * A.map PowerSeries.C).trace
      = traceSeries A d := by
  have htr : ∀ p : ℕ, coeff p ((geomSeriesMatrix A d * A.map PowerSeries.C).trace)
      = if d ∣ p then (A ^ (p / d + 1)).trace else 0 := by
    intro p
    rw [Matrix.trace, map_sum]
    refine (Finset.sum_congr rfl fun i _ => coeff_sum_geomSeriesMatrix_mul_C A d i i p).trans ?_
    split_ifs <;> simp [Matrix.trace]
  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_X_pow_mul', coeff_traceSeries]
  simpa only [htr] using ite_le_eq (fun t => (A ^ t).trace) hd m

/-- The logarithmic derivative of the local factor `det(1 - A ⬝ T ^ d)`. -/
public theorem logDerivative_localCharSeries (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.logDerivative (localCharSeries A d)
      = -(((d : ℕ) : Λ⟦X⟧) * traceSeries A d) := by
  have hu : constantCoeff (localCharSeries A d) = 1 := constantCoeff_localCharSeries A hd
  have hX : PowerSeries.X * PowerSeries.X ^ (d - 1) = (PowerSeries.X : Λ⟦X⟧) ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  have hder : PowerSeries.X * d⁄dX Λ (localCharSeries A d)
      = -(((d : ℕ) : Λ⟦X⟧) * (localCharSeries A d * traceSeries A d)) := by
    rw [localCharSeries, Derivation.map_det, map_derivative_localCharMatrix,
      adjugate_localCharMatrix A hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.trace_smul, ← X_pow_mul_trace_geomSeriesMatrix A hd, ← hX]
    simp only [smul_eq_mul, localCharSeries]
    ring
  rw [PowerSeries.logDerivative, hder]
  linear_combination (-(((d : ℕ) : Λ⟦X⟧) * traceSeries A d)) * PowerSeries.mul_invOfUnit_one hu

/-- The logarithmic derivative of the local Euler factor `det(1 - A ⬝ T ^ d) ⁻¹`. -/
public theorem logDerivative_localEulerFactor (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.logDerivative (localEulerFactor A d) = ((d : ℕ) : Λ⟦X⟧) * traceSeries A d := by
  rw [localEulerFactor,
    PowerSeries.logDerivative_invOfUnit (constantCoeff_localCharSeries A hd),
    logDerivative_localCharSeries A hd, neg_neg]

end Stacks.EtaleCohomology

end
