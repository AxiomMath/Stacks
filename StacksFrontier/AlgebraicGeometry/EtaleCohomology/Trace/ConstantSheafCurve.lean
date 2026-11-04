module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial
public import StacksFrontier.NumberTheory.TraceFormula.EigenvalueAbsoluteBound

/-!
# Constant sheaves: the L-function of a smooth projective curve

Let `k` be a finite field with `q` elements, `X` a smooth, projective, geometrically irreducible
curve over `k`, and `Λ` the coefficient ring — `ℚ_ℓ` in the source.  The constant sheaf has
trivial Galois module as stalk at every geometric point, so the local factor at a closed point
`x` is `1 - T^{deg x}` and the L-function of Tag 03UV is

`L(X, Λ) = ∏_{x ∈ |X|} (1 - T^{deg x})⁻¹`.

Section 23 of the source computes this product for a projective curve.  The cohomology is

`H^0 = Λ` with `π_X^* = 1`,  `H^1 = Λ^{2g}` with `π_X^* = A`,  `H^2 = Λ` with `π_X^* = q`,

the action on `H^2` being the one of Étale Cohomology, Lemma 0AMB together with
`deg π_X = q`.  Feeding this into the cohomological interpretation of Tag 03V0 gives the
displayed identity of the source,

`∏_{x ∈ |X|} (1 - T^{deg x})⁻¹ = det(1 - A T) / ((1 - T)(1 - q T))`,

which is `lFunction_mul_denominator_eq` below, and from it the four assertions of the lemma.

## The shape of the hypotheses

The cohomology enters as data, a genus `g` and a matrix `A` for the action of `π_X^*` on `H^1`,
exactly as elsewhere in this chapter; the identification of `H^0` and `H^2` is built into
`curveFrobenius`.  Two geometric inputs are carried as named hypotheses:

* `hcount`, that `#X(k_n) = ∑_{deg x ∣ n} deg x` — a rational point over `k_n` is a closed point
  of `X` whose residue degree divides `n`, counted `deg x` times;
* `hpoint`, Theorem 03V2 for the constant sheaf over `k_n`, that `#X(k_n)` is the alternating
  trace of `(π_X^*)^n` on the cohomology.

Together these give the hypothesis `TraceFormula` of Tag 03V0.  Part (4) needs two further
properties of the point counts, both independent of the eigenvalues: `X(k_m) ⊆ X(k_{mn})`, and
that the counts are unbounded.

The eigenvalues `α_1, …, α_{2g}` of `π_X^*` on `H^1` are a family in a ring `Ω` receiving `Λ`,
listed with multiplicity by the factorization `det(1 - A T) = ∏_i (1 - α_i T)`; the source reads
them in `ℚ̄_ℓ` and their absolute values in `ℂ`, which is the case `Ω = ℂ` of a complex
embedding.

## Main definitions

* `Stacks.EtaleCohomology.constantFrobeniusMatrices`: the Frobenius matrices of the constant
  sheaf — rank one, identity matrix, at every closed point.
* `Stacks.EtaleCohomology.constantLFunction`: `L(X, Λ) = ∏_{x ∈ |X|}(1 - T^{deg x})⁻¹`.
* `Stacks.EtaleCohomology.curveDeg`, `curveRank`, `curveFrobenius`: the cohomology of a smooth
  projective geometrically irreducible curve of genus `g` as a family indexed by `Fin 3`.
* `Stacks.EtaleCohomology.integralCurveNumerator`: the numerator `L(X, ℤ)·(1-T)(1-qT)` of the
  zeta function of `X`, formed over `ℤ` and so mentioning neither `ℓ` nor `Λ`.

## Main results

* `Stacks.EtaleCohomology.lFunction_mul_denominator_eq`: the displayed identity of §23.
* `Stacks.EtaleCohomology.isRational_constantLFunction`: part (1).
* `Stacks.EtaleCohomology.exists_integral_curveNumerator` and
  `Stacks.EtaleCohomology.isIntegral_curveEigenvalue`: part (2).
* `Stacks.EtaleCohomology.card_rationalPoints_eq_one_sub_sum_add`: part (3).
* `Stacks.EtaleCohomology.norm_curveEigenvalue_lt`: part (4).

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8), Lemma 64.23.1.
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0), the cohomological
  interpretation, applied here.
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2), the trace formula,
  carried as the hypothesis `hpoint`.
* [Stacks Project, Tag 03V9](https://stacks.math.columbia.edu/tag/03V9), the sector lemma the
  source tells us to use for part (4).
* [Stacks Project, Tag 0AMB](https://stacks.math.columbia.edu/tag/0AMB), the action on `H^2`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset Matrix PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {Λ : Type v}
  [CommRing Λ]

/-! ### The constant sheaf -/

/-- The closed points of `X` of residue degree at most `n`, the index set over which the Euler
product of the L-function is truncated.  It does not depend on the coefficient ring. -/
public def closedPointsDegreeLE (f : X ⟶ Spec (.of k)) [Finite k] [LocallyOfFiniteType f]
    [QuasiCompact f] (n : ℕ) : Finset (closedPoints X) :=
  (finite_setOf_closedPoints_residueDegree_le f n).toFinset

/-- The Frobenius matrices of the constant sheaf `Λ` on `X`: the geometric stalk at a closed
point is `Λ` with trivial Galois action, so `π_x^*` is the `1 × 1` identity matrix. -/
public def constantFrobeniusMatrices (f : X ⟶ Spec (.of k)) (Λ : Type v) [CommRing Λ] :
    FrobeniusMatrices f Λ where
  rank _ := 1
  matrix _ := 1

/-- Every Frobenius matrix of the constant sheaf has rank one. -/
public theorem rank_constantFrobeniusMatrices (x : closedPoints X) :
    (constantFrobeniusMatrices f Λ).rank x = 1 :=
  rfl

/-- The Frobenius matrix of the constant sheaf at every closed point is the identity. -/
public theorem matrix_constantFrobeniusMatrices (x : closedPoints X) :
    (constantFrobeniusMatrices f Λ).matrix x = 1 :=
  rfl

section

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The support in degree `n` of the Euler system of the constant sheaf is the set of closed
points of residue degree at most `n`. -/
public theorem support_eulerSystem_constantFrobeniusMatrices (n : ℕ) :
    (constantFrobeniusMatrices f Λ).eulerSystem.support n = closedPointsDegreeLE f n :=
  rfl

end

/-- The L-function `L(X, Λ) = ∏_{x ∈ |X|} (1 - T^{deg x})⁻¹` of the constant sheaf, the
specialization of Tag 03UV to the sheaf considered in §23. -/
public def constantLFunction (f : X ⟶ Spec (.of k)) (Λ : Type v) [CommRing Λ] [Finite k]
    [LocallyOfFiniteType f] [QuasiCompact f] : Λ⟦X⟧ :=
  (constantFrobeniusMatrices f Λ).lFunction

/-- The local factor of the constant sheaf at a closed point is `(1 - T^{deg x})⁻¹`. -/
public theorem localFactor_constantFrobeniusMatrices (x : closedPoints X) :
    (constantFrobeniusMatrices f Λ).localFactor x
      = localEulerFactor (1 : Matrix (Fin 1) (Fin 1) Λ) (residueDegree f x.1) :=
  rfl

section

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The L-function of the constant sheaf is formed over `ℤ` and base changed: its coefficients
are the images of integers computed by the same Euler product over `ℤ`. -/
public theorem map_constantLFunction {Λ' : Type*} [CommRing Λ'] (φ : Λ →+* Λ') :
    PowerSeries.map φ (constantLFunction f Λ) = constantLFunction f Λ' := by
  rw [constantLFunction, constantLFunction, FrobeniusMatrices.map_lFunction]
  refine FrobeniusMatrices.lFunction_congr _ fun x => ?_
  rw [FrobeniusMatrices.localFactor, FrobeniusMatrices.localFactor]
  congr 1
  exact Matrix.map_one φ (map_zero φ) (map_one φ)

/-! ### The cohomology of a projective curve -/

/-- The cohomological degrees `0`, `1`, `2` in which a curve has cohomology. -/
public def curveDeg : Fin 3 → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The ranks `1`, `2g`, `1` of the cohomology of a smooth projective geometrically irreducible
curve of genus `g`. -/
public def curveRank (g : ℕ) : Fin 3 → ℕ
  | 0 => 1
  | 1 => 2 * g
  | 2 => 1

/-- The matrices of `π_X^*` on the cohomology of a smooth projective geometrically irreducible
curve of genus `g` over a field with `q` elements: the identity on `H^0 = Λ`, the given matrix
`A` on `H^1 = Λ^{2g}`, and multiplication by `q` on `H^2 = Λ`.  The last is Étale Cohomology,
Lemma 0AMB together with the degree of `π_X` being `q`. -/
public def curveFrobenius (q : ℕ) {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) :
    ∀ a : Fin 3, Matrix (Fin (curveRank g a)) (Fin (curveRank g a)) Λ
  | 0 => 1
  | 1 => A
  | 2 => Matrix.diagonal fun _ => (q : Λ)

/-- The alternating product of Tag 03V0 for a projective curve, with the three cohomological
factors spelled out. -/
public theorem alternatingCharSeries_curveFrobenius (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) :
    alternatingCharSeries curveDeg (curveRank g) (curveFrobenius q A)
      = localEulerFactor (1 : Matrix (Fin 1) (Fin 1) Λ) 1 * localCharSeries A 1 *
          localEulerFactor (Matrix.diagonal fun _ : Fin 1 => (q : Λ)) 1 := by
  rw [alternatingCharSeries, Fin.prod_univ_three]
  norm_num [curveDeg, curveRank, curveFrobenius]
  rfl

/-- **The displayed identity of §23.**  Multiplying the alternating product of Tag 03V0 by
`(1 - T)(1 - qT)` leaves `det(1 - π_X^* T |_{H^1})`. -/
public theorem alternatingCharSeries_curveFrobenius_mul (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) :
    alternatingCharSeries curveDeg (curveRank g) (curveFrobenius q A) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C (q : Λ) * PowerSeries.X))
      = localCharSeries A 1 := by
  have h0 : localCharSeries (1 : Matrix (Fin 1) (Fin 1) Λ) 1 = 1 - PowerSeries.X := by
    simpa using localCharSeries_one_fin_one (Λ := Λ) 1
  have h2 : localCharSeries (Matrix.diagonal fun _ : Fin 1 => (q : Λ)) 1
      = 1 - PowerSeries.C (q : Λ) * PowerSeries.X := by
    simpa using localCharSeries_diagonal_fin_one (q : Λ) 1
  have e0 := localCharSeries_mul_localEulerFactor (1 : Matrix (Fin 1) (Fin 1) Λ) one_ne_zero
  have e2 := localCharSeries_mul_localEulerFactor
    (Matrix.diagonal fun _ : Fin 1 => (q : Λ)) one_ne_zero
  rw [h0] at e0
  rw [h2] at e2
  rw [alternatingCharSeries_curveFrobenius]
  linear_combination (localCharSeries A 1 *
      localEulerFactor (Matrix.diagonal fun _ : Fin 1 => (q : Λ)) 1 *
      (1 - PowerSeries.C (q : Λ) * PowerSeries.X)) * e0 + localCharSeries A 1 * e2

/-! ### The trace formula for the constant sheaf -/

/-- The alternating trace of `(π_X^*)^n` on the cohomology of a projective curve. -/
public theorem alternatingTrace_curveFrobenius (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (n : ℕ) :
    ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace
      = 1 - (A ^ n).trace + (q : Λ) ^ n := by
  rw [Fin.sum_univ_three]
  norm_num [curveDeg, curveRank, curveFrobenius, Matrix.diagonal_pow, Matrix.trace_diagonal]
  exact (sub_eq_add_neg _ _).symm

/-- The two geometric inputs — the decomposition of `X(k_n)` into closed points of divisor
degree and Theorem 03V2 for the constant sheaf — give the hypothesis `TraceFormula` of Tag
03V0. -/
public theorem traceFormula_constantFrobeniusMatrices (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    (constantFrobeniusMatrices f Λ).TraceFormula curveDeg (curveRank g)
      (curveFrobenius q A) := by
  intro m hm
  have hleft : ∑ x ∈ ((constantFrobeniusMatrices f Λ).eulerSystem.support m).filter
        fun x => residueDegree f x.1 ∣ m,
        (residueDegree f x.1 : Λ) *
          (((constantFrobeniusMatrices f Λ).matrix x) ^ (m / residueDegree f x.1)).trace
      = (N m : Λ) := by
    rw [support_eulerSystem_constantFrobeniusMatrices, hcount m hm, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [matrix_constantFrobeniusMatrices, one_pow, Matrix.trace_one,
      rank_constantFrobeniusMatrices]
    simp
  exact hleft.trans (hpoint m hm)

/-- The cohomological interpretation of Tag 03V0 for the constant sheaf on a projective
curve. -/
public theorem constantLFunction_eq_alternatingCharSeries [IsAddTorsionFree Λ] (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    constantLFunction f Λ
      = alternatingCharSeries curveDeg (curveRank g) (curveFrobenius q A) :=
  FrobeniusMatrices.lFunction_eq_alternatingCharSeries _ _ _ _
    (traceFormula_constantFrobeniusMatrices q A N hcount hpoint)

/-- **The identity the source displays before the lemma.**
`∏_{x ∈ |X|}(1 - T^{deg x})⁻¹ · (1 - T)(1 - qT) = det(1 - π_X^* T |_{H^1})`. -/
public theorem lFunction_mul_denominator_eq [IsAddTorsionFree Λ] (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    constantLFunction f Λ * ((1 - PowerSeries.X) * (1 - PowerSeries.C (q : Λ) * PowerSeries.X))
      = localCharSeries A 1 := by
  rw [constantLFunction_eq_alternatingCharSeries q A N hcount hpoint]
  exact alternatingCharSeries_curveFrobenius_mul q A

/-! ### Part (1): rationality -/

private lemma coe_denominator (c : Λ) :
    (((1 - Polynomial.X) * (1 - Polynomial.C c * Polynomial.X) : Polynomial Λ) : Λ⟦X⟧)
      = (1 - PowerSeries.X) * (1 - PowerSeries.C c * PowerSeries.X) := by
  push_cast [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
    Polynomial.coe_C]
  ring

/-- **Tag 03V8, part (1).**  The L-function `L(X, Λ)` of the constant sheaf on a smooth,
projective, geometrically irreducible curve over a finite field is a rational function: its
product with the polynomial `(1 - T)(1 - qT)`, whose value at `0` is `1`, is the polynomial
`det(1 - π_X^* T |_{H^1})`. -/
public theorem isRational_constantLFunction [IsAddTorsionFree Λ] [Nontrivial Λ] (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    ∃ P Q : Polynomial Λ, Q.eval 0 ≠ 0 ∧
      constantLFunction f Λ * (Q : Λ⟦X⟧) = (P : Λ⟦X⟧) := by
  refine ⟨localCharPolynomial A 1,
    (1 - Polynomial.X) * (1 - Polynomial.C (q : Λ) * Polynomial.X), ?_, ?_⟩
  · simp
  · rw [coe_denominator, coe_localCharPolynomial]
    exact lFunction_mul_denominator_eq q A N hcount hpoint

/-! ### Eigenvalues and traces -/

/-- If `det(1 - A T) = ∏_i (1 - α_i T)`, that is if `α_1, …, α_n` are the eigenvalues of `A`
with multiplicity, then `tr(A^m) = ∑_i α_i^m` for every `m ≥ 1`.  Both sides are read off the
logarithmic derivative of the local factor. -/
public theorem trace_pow_eq_sum_pow {Ω : Type*} [CommRing Ω] {n : Type w} [Fintype n]
    [DecidableEq n] {ι : Type*} [Fintype ι] {A : Matrix n n Ω} {α : ι → Ω}
    (hα : localCharSeries A 1 = ∏ i, (1 - PowerSeries.C (α i) * PowerSeries.X))
    {m : ℕ} (hm : m ≠ 0) : (A ^ m).trace = ∑ i, α i ^ m := by
  have hfac : ∀ i : ι, (1 - PowerSeries.C (α i) * PowerSeries.X)
      = localCharSeries (Matrix.diagonal fun _ : Fin 1 => α i) 1 := by
    intro i
    simpa using (localCharSeries_diagonal_fin_one (α i) 1).symm
  have hα' : localCharSeries A 1
      = ∏ i, localCharSeries (Matrix.diagonal fun _ : Fin 1 => α i) 1 := by
    rw [hα]
    exact Finset.prod_congr rfl fun i _ => hfac i
  have hlog : PowerSeries.logDerivative (localCharSeries A 1)
      = ∑ i, PowerSeries.logDerivative
          (localCharSeries (Matrix.diagonal fun _ : Fin 1 => α i) 1) := by
    rw [hα']
    exact PowerSeries.logDerivative_finsetProd _ _
      fun i _ => constantCoeff_localCharSeries _ one_ne_zero
  have hL : PowerSeries.logDerivative (localCharSeries A 1) = -traceSeries A 1 := by
    rw [logDerivative_localCharSeries A one_ne_zero]
    simp
  have hR : ∀ i : ι, PowerSeries.logDerivative
      (localCharSeries (Matrix.diagonal fun _ : Fin 1 => α i) 1)
      = -traceSeries (Matrix.diagonal fun _ : Fin 1 => α i) 1 := by
    intro i
    rw [logDerivative_localCharSeries _ one_ne_zero]
    simp
  rw [hL, Finset.sum_congr rfl fun i _ => hR i] at hlog
  have hc := congrArg (PowerSeries.coeff m) hlog
  rw [map_neg, map_sum] at hc
  simp only [map_neg, coeff_traceSeries, one_dvd, hm, ne_eq, not_false_eq_true, and_true,
    if_true, Nat.div_one, Matrix.diagonal_pow, Matrix.trace_diagonal, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, one_smul, Pi.pow_apply] at hc
  refine neg_inj.1 ?_
  rw [hc]
  simp

/-- Base change of the eigenvalue factorization: the trace of a power of `A` is sent to the
sum of the powers of the eigenvalues. -/
public theorem map_trace_pow_eq_sum_pow {Ω : Type*} [CommRing Ω] {n : Type w} [Fintype n]
    [DecidableEq n] {ι : Type*} [Fintype ι] {A : Matrix n n Λ} (φ : Λ →+* Ω) {α : ι → Ω}
    (hα : (localCharPolynomial A 1).map φ = ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    {m : ℕ} (hm : m ≠ 0) : φ ((A ^ m).trace) = ∑ i, α i ^ m := by
  have hmapA : (A ^ m).map φ = (A.map φ) ^ m := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  have htr : φ ((A ^ m).trace) = (((A ^ m).map φ)).trace := by
    rw [Matrix.trace, Matrix.trace, map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hcoe : ∀ p : Polynomial Λ,
      PowerSeries.map φ (p : Λ⟦X⟧) = ((p.map φ : Polynomial Ω) : Ω⟦X⟧) := by
    intro p
    ext j
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]
  have hprod : ((∏ i, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial Ω) : Ω⟦X⟧)
      = ∏ i, (1 - PowerSeries.C (α i) * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  have hser : localCharSeries (A.map φ) 1
      = ∏ i, (1 - PowerSeries.C (α i) * PowerSeries.X) := by
    rw [← map_localCharSeries_eq φ A 1, ← coe_localCharPolynomial A 1, hcoe, hα, hprod]
  rw [htr, hmapA]
  exact trace_pow_eq_sum_pow hser hm

/-! ### Part (3): the number of rational points -/

/-- **Part (3) of Tag 03V8.**  The number of rational points of `X` over the extension `k_n` of
degree `n` is `1 - ∑_{i = 1}^{2g} α_i^n + q^n`, where `α_1, …, α_{2g}` are the eigenvalues of
`π_X^*` on `H^1`. -/
public theorem card_rationalPoints_eq_one_sub_sum_add (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace)
    {Ω : Type*} [CommRing Ω] (φ : Λ →+* Ω) (α : Fin (2 * g) → Ω)
    (hα : (localCharPolynomial A 1).map φ = ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    {n : ℕ} (hn : n ≠ 0) :
    (N n : Ω) = 1 - ∑ i, α i ^ n + (q : Ω) ^ n := by
  have h := hpoint n hn
  rw [alternatingTrace_curveFrobenius q A n] at h
  have hφ := congrArg φ h
  rw [map_natCast] at hφ
  rw [hφ, map_add, map_sub, map_one, map_pow, map_natCast,
    map_trace_pow_eq_sum_pow φ hα hn]

end

/-! ### Part (2): integrality and independence of `ℓ` -/

/-- The numerator of the zeta function of `X`: the L-function of the constant sheaf formed over
`ℤ`, multiplied by `(1 - T)(1 - qT)`.  Neither `ℓ` nor the coefficient ring `Λ` appears in it,
which is the sense in which the data it records is independent of `ℓ`. -/
public def integralCurveNumerator (f : X ⟶ Spec (.of k)) [Finite k] [LocallyOfFiniteType f]
    [QuasiCompact f] (q : ℕ) : PowerSeries ℤ :=
  constantLFunction f ℤ * ((1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℤ) * PowerSeries.X))

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- `det(1 - π_X^* T |_{H^1})` is the image of the integral numerator of the zeta function. -/
public theorem localCharSeries_eq_map_integralCurveNumerator [IsAddTorsionFree Λ] (q : ℕ)
    {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    localCharSeries A 1
      = PowerSeries.map (Int.castRingHom Λ) (integralCurveNumerator f q) := by
  have hden : PowerSeries.map (Int.castRingHom Λ)
      ((1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℤ) * PowerSeries.X))
      = (1 - PowerSeries.X) * (1 - PowerSeries.C (q : Λ) * PowerSeries.X) := by
    simp only [map_mul, map_sub, map_one, PowerSeries.map_X, PowerSeries.map_C]
    norm_num
  rw [integralCurveNumerator, map_mul, map_constantLFunction, hden]
  exact (lFunction_mul_denominator_eq q A N hcount hpoint).symm

/-- **Tag 03V8, part (2), independence of `ℓ`.**  The characteristic polynomial
`det(1 - π_X^* T |_{H^1})` is the image of a polynomial over `ℤ` of degree at most `2g` with
constant coefficient `1`, pinned by the integral numerator of the zeta function of `X` — data
in which neither `ℓ` nor the coefficient ring occurs. -/
public theorem exists_integral_curveNumerator [IsAddTorsionFree Λ] [CharZero Λ] (q : ℕ)
    {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * g ∧ P.coeff 0 = 1 ∧
      (P : PowerSeries ℤ) = integralCurveNumerator f q ∧
      P.map (Int.castRingHom Λ) = localCharPolynomial A 1 := by
  have hmap := localCharSeries_eq_map_integralCurveNumerator q A N hcount hpoint
  have hcoeff : ∀ m : ℕ, ((PowerSeries.coeff m (integralCurveNumerator f q) : ℤ) : Λ)
      = (localCharPolynomial A 1).coeff m := by
    intro m
    have h := congrArg (PowerSeries.coeff m) hmap
    rw [← coe_localCharPolynomial, Polynomial.coeff_coe, PowerSeries.coeff_map] at h
    exact h.symm
  have hdegA : (localCharPolynomial A 1).natDegree ≤ 2 * g := by
    simpa using natDegree_localCharPolynomial_le A 1
  have hvanish : ∀ m : ℕ, 2 * g < m → PowerSeries.coeff m (integralCurveNumerator f q) = 0 := by
    intro m hm
    exact_mod_cast (hcoeff m).trans (Polynomial.natDegree_le_iff_coeff_eq_zero.1 hdegA m hm)
  refine ⟨PowerSeries.trunc (2 * g + 1) (integralCurveNumerator f q), ?_, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    rw [PowerSeries.coeff_trunc, if_neg (by lia)]
  · rw [PowerSeries.coeff_trunc, if_pos (by lia)]
    exact_mod_cast (hcoeff 0).trans (coeff_zero_localCharPolynomial A one_ne_zero)
  · ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with h
    · rfl
    · exact (hvanish m (by lia)).symm
  · ext m
    rw [Polynomial.coeff_map, PowerSeries.coeff_trunc]
    split_ifs with h
    · exact hcoeff m
    · rw [map_zero]
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero.1 hdegA m (by lia)).symm

/-- Mapping an integral polynomial to `Ω` directly or through `Λ` and `φ` gives the same result. -/
private lemma map_intCastRingHom_eq_map {Ω : Type*} [CommRing Ω] (φ : Λ →+* Ω)
    {P : Polynomial ℤ} {Q : Polynomial Λ} (h : P.map (Int.castRingHom Λ) = Q) :
    P.map (Int.castRingHom Ω) = Q.map φ := by
  rw [← h, Polynomial.map_map, RingHom.ext_int (φ.comp _) (Int.castRingHom Ω)]

/-- **Tag 03V8, part (2), integrality.**  The eigenvalues of `π_X^*` on `H^1` are algebraic
integers: they are the reciprocal roots of an integral polynomial with constant coefficient
`1`. -/
public theorem isIntegral_curveEigenvalue [IsAddTorsionFree Λ] [CharZero Λ] (q : ℕ) {g : ℕ}
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace)
    {Ω : Type*} [CommRing Ω] (φ : Λ →+* Ω) (α : Fin (2 * g) → Ω)
    (hα : (localCharPolynomial A 1).map φ = ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    (i : Fin (2 * g)) : IsIntegral ℤ (α i) := by
  obtain ⟨P, hdeg, h0, -, hPmap⟩ := exists_integral_curveNumerator q A N hcount hpoint
  exact isIntegral_of_prod_one_sub_C_mul_X_eq_map α (by simpa using hdeg) h0
    ((map_intCastRingHom_eq_map φ hPmap).trans hα) i

/-! ### Part (4): the archimedean bound -/

/-- **Tag 03V8, part (4).**  Every eigenvalue of `π_X^*` on `H^1`, read in `ℂ` along a complex
embedding of the coefficient field, has absolute value strictly less than `q`. -/
public theorem norm_curveEigenvalue_lt [IsAddTorsionFree Λ] [CharZero Λ] {q : ℕ} (hq : 1 < q)
    {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Λ) else -1) *
        ((curveFrobenius q A a) ^ n).trace)
    (hmono : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → N m ≤ N (m * n))
    (hunbdd : ∀ C : ℕ, ∃ m : ℕ, m ≠ 0 ∧ C < N m)
    (φ : Λ →+* ℂ) (α : Fin (2 * g) → ℂ)
    (hα : (localCharPolynomial A 1).map φ = ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    (i : Fin (2 * g)) : ‖α i‖ < (q : ℝ) := by
  obtain ⟨P, hdeg, h0, -, hPmap⟩ := exists_integral_curveNumerator q A N hcount hpoint
  obtain ⟨Q, hmonic, hQmap⟩ := exists_monic_map_eq_prod_X_sub_C α (by simpa using hdeg) h0
    ((map_intCastRingHom_eq_map φ hPmap).trans hα)
  refine Stacks.TraceFormula.norm_lt_of_pointCount α hq N (fun m hm => ?_) hmono hunbdd
    (fun j => Stacks.TraceFormula.exists_conj_eq_of_monic_map_eq_prod α hmonic hQmap j) i
  exact card_rationalPoints_eq_one_sub_sum_add q A N hpoint φ α hα hm

end Stacks.EtaleCohomology

end
