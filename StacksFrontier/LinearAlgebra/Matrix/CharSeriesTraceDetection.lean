module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.FreeModuleTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces of powers detect characteristic series over a ring with torsion-free `R^♮`

Let `R` be a ring, not necessarily commutative, and `R^♮ = R/[R,R]` its additive commutator
quotient. Let `φ : R → M_r(Λ)` be a ring map to matrices over a commutative ring `Λ`. For a
square matrix `A` over `R`, the characteristic series `det_Λ(1 - φ(A) T)` is in general not
determined by the classes in `R^♮` of the traces of the powers of `A`: over `R = Λ = 𝔽_ℓ`, the
identity matrix of size `ℓ` has all these traces zero, but characteristic series
`(1 - T) ^ ℓ ≠ 1`.

The determination does hold up to `T ^ N` under a torsion hypothesis on `R^♮` relative to `φ`.
The hypothesis is automatic when `R^♮` has no torsion, for instance for `R = ℤ_ℓ[G]`. It holds
for `R = ℤ/ℓ^M[G]` when `M` is large compared to `N` and to the exponent of `Λ`, which is the
case used for the finite-coefficient cohomological interpretation of L-functions (Stacks 03UZ).

## Main definitions

* `TraceDetectionHypothesis`: the torsion hypothesis `(H_N)` on `R^♮` relative to `φ`.
* `tau`: the logarithmic derivative `τ(z) = [tr(z⁻¹ · T dz/dT)]` of a power series over
  `M_n(R)`.
* `delta`: the determinant `δ(z) = det_Λ(φ(z))` of a power series over `M_n(R)`.

## Main results

* `coeff_delta_eq_zero_of_tau`: under `(H_N)`, if `z ≡ 1 (mod T)` and `τ(z)` vanishes in degrees
  `1, …, N`, then `δ(z) ≡ 1 (mod T ^ (N + 1))`.
* `coeff_det_eq_of_trace_pow`: under `(H_N)`, if `[tr(A ^ m)] = [tr(B ^ m)]` in `R^♮` for
  `1 ≤ m ≤ N`, then `det_Λ(1 - φ(A) T) ≡ det_Λ(1 - φ(B) T) (mod T ^ (N + 1))`.

## Implementation notes

Work in the ring `S⟦T⟧` of power series over `S = M_n(R)`. For an element `z` with constant
coefficient `1`, the logarithmic derivative `τ(z)` is additive, `τ(zw) = τ(z) + τ(w)`, by
cyclicity of the trace in `R^♮`. On `z = 1 - A T` it gives `τ = -∑_{m ≥ 1} [tr(A ^ m)] T ^ m`.
The determinant `δ` is multiplicative. If `τ(z) ≡ 0 (mod T ^ (N + 1))`, the lowest nontrivial
coefficient of `z` can be removed by a factor `v` with `δ(v) = 1` and `τ(v) = 0`, a product of
elementary matrices and a diagonal matrix built from `(1 + a b T^k)(1 + b a T^k)⁻¹`.
-/

@[expose] public noncomputable section

open PowerSeries Matrix
open scoped BigOperators

universe u v

namespace Stacks.CharSeriesTraceDetection

open CategoryTheory.FilteredDerived

variable {R : Type u} [Ring R]

/-! ### The class of the trace in `R^♮` -/

/-- The class in `R^♮` of an element of `R`. -/
abbrev q (R : Type u) [Ring R] : R →+ AdditiveCommutatorQuotient R :=
  additiveCommutatorQuotientMk R

/-- The classes of `a * b` and `b * a` in `R^♮` agree. -/
theorem q_mul_comm (a b : R) : q R (a * b) = q R (b * a) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (QuotientAddGroup.eq_zero_iff _).2
    (AddSubgroup.subset_closure ⟨a, b, rfl⟩)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The class in `R^♮` of the trace of a square matrix over `R`. -/
def trq (n : Type*) [Fintype n] : Matrix n n R →+ AdditiveCommutatorQuotient R :=
  (q R).comp (Matrix.traceAddMonoidHom n R)

omit [DecidableEq n] in
/-- `trq n A` is the class in `R^♮` of the trace of `A`. -/
theorem trq_apply (A : Matrix n n R) : trq n A = q R (Matrix.trace A) := rfl

omit [DecidableEq n] in
/-- The class in `R^♮` of the trace is cyclic: `[tr(AB)] = [tr(BA)]`. -/
theorem trq_mul_comm (A B : Matrix n n R) : trq n (A * B) = trq n (B * A) := by
  simp only [trq_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact q_mul_comm _ _

/-- The class of the trace of the `m`-th coefficient of a power series over `M_n(R)`. -/
def trCoeff (n : Type*) [Fintype n] [DecidableEq n] (m : ℕ) : PowerSeries (Matrix n n R) →+
    AdditiveCommutatorQuotient R where
  toFun f := trq n (coeff m f)
  map_zero' := by simp
  map_add' f g := by simp

/-- `trCoeff n m f` is the class of the trace of the `m`-th coefficient of `f`. -/
theorem trCoeff_apply (m : ℕ) (f : PowerSeries (Matrix n n R)) :
    trCoeff n m f = trq n (coeff m f) := rfl

/-- **Cyclicity of the trace, coefficientwise.** -/
@[sga "4½ Rapport 4.2" "special case"]
theorem trCoeff_mul_comm (m : ℕ) (f g : PowerSeries (Matrix n n R)) :
    trCoeff n m (f * g) = trCoeff n m (g * f) := by
  rw [trCoeff_apply, trCoeff_apply, coeff_mul, coeff_mul, map_sum, map_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact trq_mul_comm _ _

/-! ### The degree derivation `T d/dT` -/

/-- The derivation `T d/dT` on power series over a (noncommutative) ring. -/
def degDeriv {S : Type*} [Ring S] (f : PowerSeries S) : PowerSeries S :=
  PowerSeries.mk fun m => (m : ℕ) • coeff m f

/-- The `m`-th coefficient of `T df/dT` is `m` times the `m`-th coefficient of `f`. -/
theorem coeff_degDeriv {S : Type*} [Ring S] (m : ℕ) (f : PowerSeries S) :
    coeff m (degDeriv f) = (m : ℕ) • coeff m f := coeff_mk _ _

/-- The Leibniz rule for `T d/dT`. -/
theorem degDeriv_mul {S : Type*} [Ring S] (f g : PowerSeries S) :
    degDeriv (f * g) = degDeriv f * g + f * degDeriv g := by
  ext m
  simp only [coeff_degDeriv, map_add, coeff_mul, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [smul_mul_assoc, mul_smul_comm, ← add_smul, hp]

/-- `T d/dT` is additive. -/
theorem degDeriv_add {S : Type*} [Ring S] (f g : PowerSeries S) :
    degDeriv (f + g) = degDeriv f + degDeriv g := by
  ext m
  simp [coeff_degDeriv, smul_add]

/-- `T d/dT` kills `1`. -/
theorem degDeriv_one {S : Type*} [Ring S] : degDeriv (1 : PowerSeries S) = 0 := by
  ext m
  rw [coeff_degDeriv, coeff_one]
  split_ifs with h <;> simp [h]

/-! ### Inverses of power series with constant coefficient `1` -/

section Inverse

variable {S : Type*} [Ring S]

/-- The inverse of a power series with constant coefficient `1`. -/
abbrev inv1 (z : PowerSeries S) : PowerSeries S := PowerSeries.invOfUnit z 1

/-- `inv1 z` is a right inverse of `z` when `z` has constant coefficient `1`. -/
theorem mul_inv1 {z : PowerSeries S} (hz : constantCoeff z = 1) : z * inv1 z = 1 :=
  PowerSeries.mul_invOfUnit z 1 (by simpa using hz)

/-- `inv1 z` is a left inverse of `z` when `z` has constant coefficient `1`. -/
theorem inv1_mul {z : PowerSeries S} (hz : constantCoeff z = 1) : inv1 z * z = 1 :=
  PowerSeries.invOfUnit_mul z 1 (by simpa using hz)

/-- The constant coefficient of `inv1 z` is `1`. -/
theorem constantCoeff_inv1 (z : PowerSeries S) : constantCoeff (inv1 z) = 1 := by
  simp [inv1, PowerSeries.constantCoeff_invOfUnit]

/-- A right inverse of a power series with constant coefficient `1` is its inverse. -/
theorem inv1_eq_of_mul_eq_one {z w : PowerSeries S} (hz : constantCoeff z = 1)
    (h : z * w = 1) : inv1 z = w := by
  calc inv1 z = inv1 z * (z * w) := by rw [h, mul_one]
    _ = w := by rw [← mul_assoc, inv1_mul hz, one_mul]

/-- `(z w)⁻¹ = w⁻¹ z⁻¹` for power series with constant coefficient `1`. -/
theorem inv1_mul_inv1 {z w : PowerSeries S} (hz : constantCoeff z = 1)
    (hw : constantCoeff w = 1) : inv1 (z * w) = inv1 w * inv1 z := by
  refine inv1_eq_of_mul_eq_one (by simp [hz, hw]) ?_
  rw [mul_assoc, ← mul_assoc w, mul_inv1 hw, one_mul, mul_inv1 hz]

end Inverse

/-! ### The logarithmic derivative `τ(z) = [tr(z⁻¹ · T dz/dT)]` -/

/-- The `m`-th coefficient of the logarithmic derivative `[tr(z⁻¹ · T dz/dT)]` of a power series
over `M_n(R)`. -/
def tau (z : PowerSeries (Matrix n n R)) (m : ℕ) : AdditiveCommutatorQuotient R :=
  trCoeff n m (inv1 z * degDeriv z)

/-- `trCoeff` is invariant under conjugation `x ↦ w⁻¹ x w`. -/
theorem trCoeff_conj (m : ℕ) {w : PowerSeries (Matrix n n R)} (hw : constantCoeff w = 1)
    (x : PowerSeries (Matrix n n R)) : trCoeff n m (inv1 w * x * w) = trCoeff n m x := by
  rw [mul_assoc, trCoeff_mul_comm, mul_assoc, mul_inv1 hw, mul_one]

/-- **The logarithmic derivative is additive.** -/
theorem tau_mul {z w : PowerSeries (Matrix n n R)} (hz : constantCoeff z = 1)
    (hw : constantCoeff w = 1) (m : ℕ) : tau (z * w) m = tau z m + tau w m := by
  rw [tau, inv1_mul_inv1 hz hw, degDeriv_mul, mul_add, map_add]
  congr 1
  · rw [show inv1 w * inv1 z * (degDeriv z * w) = inv1 w * (inv1 z * degDeriv z) * w by
      simp only [mul_assoc], trCoeff_conj m hw]
    rfl
  · rw [show inv1 w * inv1 z * (z * degDeriv w) = inv1 w * degDeriv w by
      rw [mul_assoc, ← mul_assoc (inv1 z), inv1_mul hz, one_mul]]
    rfl

/-- `τ(1) = 0`. -/
theorem tau_one (m : ℕ) : tau (1 : PowerSeries (Matrix n n R)) m = 0 := by
  simp [tau, degDeriv_one]

/-- `τ(z⁻¹) = -τ(z)`. -/
theorem tau_inv1 {z : PowerSeries (Matrix n n R)} (hz : constantCoeff z = 1) (m : ℕ) :
    tau (inv1 z) m = -tau z m := by
  have h := tau_mul hz (constantCoeff_inv1 z) m
  rw [mul_inv1 hz, tau_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm


/-! ### The coefficientwise trace class on power series over `R` -/

/-- The class in `R^♮` of the `m`-th coefficient of a power series over `R`. -/
def qCoeff (m : ℕ) : PowerSeries R →+ AdditiveCommutatorQuotient R where
  toFun f := q R (coeff m f)
  map_zero' := by simp
  map_add' f g := by simp

/-- `qCoeff m f` is the class in `R^♮` of the `m`-th coefficient of `f`. -/
theorem qCoeff_apply (m : ℕ) (f : PowerSeries R) : qCoeff m f = q R (coeff m f) := rfl

/-- The coefficientwise class in `R^♮` of `f * g` equals that of `g * f`. -/
theorem qCoeff_mul_comm (m : ℕ) (f g : PowerSeries R) : qCoeff m (f * g) = qCoeff m (g * f) := by
  rw [qCoeff_apply, qCoeff_apply, coeff_mul, coeff_mul, map_sum, map_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.sum_congr rfl fun p _ => q_mul_comm _ _

/-- The logarithmic derivative of a power series over `R`. -/
def tau₁ (u : PowerSeries R) (m : ℕ) : AdditiveCommutatorQuotient R :=
  qCoeff m (inv1 u * degDeriv u)

/-! ### Diagonal power series -/

/-- The diagonal power series over `M_n(R)` with diagonal entries `u i`. -/
def diagPS (u : n → PowerSeries R) : PowerSeries (Matrix n n R) :=
  PowerSeries.mk fun m => Matrix.diagonal fun i => coeff m (u i)

/-- The `m`-th coefficient of `diagPS u` is the diagonal matrix of the `m`-th coefficients. -/
theorem coeff_diagPS (u : n → PowerSeries R) (m : ℕ) :
    coeff m (diagPS u) = Matrix.diagonal fun i => coeff m (u i) := coeff_mk _ _

/-- `diagPS` is multiplicative. -/
theorem diagPS_mul (u w : n → PowerSeries R) : diagPS (u * w) = diagPS u * diagPS w := by
  ext m : 1
  rw [coeff_mul, coeff_diagPS]
  simp only [coeff_diagPS, Matrix.diagonal_mul_diagonal, Pi.mul_apply, coeff_mul]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.sum_apply]

/-- `diagPS 1 = 1`. -/
theorem diagPS_one : diagPS (1 : n → PowerSeries R) = 1 := by
  ext m : 1
  rw [coeff_diagPS, coeff_one]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The constant coefficient of `diagPS u` is the diagonal matrix of constant coefficients. -/
theorem constantCoeff_diagPS (u : n → PowerSeries R) :
    constantCoeff (diagPS u) = Matrix.diagonal fun i => constantCoeff (u i) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_diagPS]
  simp

/-- `T d/dT` commutes with `diagPS`. -/
theorem degDeriv_diagPS (u : n → PowerSeries R) :
    degDeriv (diagPS u) = diagPS fun i => degDeriv (u i) := by
  ext m : 1
  simp only [coeff_degDeriv, coeff_diagPS]
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The inverse of `diagPS u` is the diagonal power series of the inverses of the entries. -/
theorem inv1_diagPS {u : n → PowerSeries R} (hu : ∀ i, constantCoeff (u i) = 1) :
    inv1 (diagPS u) = diagPS fun i => inv1 (u i) := by
  refine inv1_eq_of_mul_eq_one (by simp [constantCoeff_diagPS, hu]) ?_
  rw [← diagPS_mul, ← diagPS_one]
  congr 1
  funext i
  exact mul_inv1 (hu i)

/-- The trace class of a coefficient of `diagPS u` is the sum of the classes of its entries. -/
theorem trCoeff_diagPS (u : n → PowerSeries R) (m : ℕ) :
    trCoeff n m (diagPS u) = ∑ i, qCoeff m (u i) := by
  simp [trCoeff_apply, trq_apply, coeff_diagPS, Matrix.trace_diagonal, qCoeff_apply]

/-- **`τ` of a diagonal power series is the sum of the `τ`'s of its entries.** -/
theorem tau_diagPS {u : n → PowerSeries R} (hu : ∀ i, constantCoeff (u i) = 1) (m : ℕ) :
    tau (diagPS u) m = ∑ i, tau₁ (u i) m := by
  rw [tau, inv1_diagPS hu, degDeriv_diagPS, ← diagPS_mul, trCoeff_diagPS]
  rfl

/-- The logarithmic derivative `τ₁` is additive. -/
theorem tau₁_mul {u w : PowerSeries R} (hu : constantCoeff u = 1) (hw : constantCoeff w = 1)
    (m : ℕ) : tau₁ (u * w) m = tau₁ u m + tau₁ w m := by
  have h := tau_mul (n := Fin 1) (z := diagPS fun _ => u) (w := diagPS fun _ => w)
    (by simp [constantCoeff_diagPS, hu]) (by simp [constantCoeff_diagPS, hw]) m
  rw [← diagPS_mul, tau_diagPS (fun _ => by simp [hu, hw]), tau_diagPS (fun _ => hu),
    tau_diagPS (fun _ => hw)] at h
  simpa using h

/-- `τ₁(u⁻¹) = -τ₁(u)`. -/
theorem tau₁_inv1 {u : PowerSeries R} (hu : constantCoeff u = 1) (m : ℕ) :
    tau₁ (inv1 u) m = -tau₁ u m := by
  have h := tau₁_mul hu (constantCoeff_inv1 u) m
  rw [mul_inv1 hu, show tau₁ (1 : PowerSeries R) m = 0 by simp [tau₁, degDeriv_one]] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Push-through for inverses: `(1 + αβ)⁻¹ α = α (1 + βα)⁻¹`. -/
private theorem inv1_one_add_mul_mul {α β : PowerSeries R} (h : constantCoeff (α * β) = 0)
    (h' : constantCoeff (β * α) = 0) : inv1 (1 + α * β) * α = α * inv1 (1 + β * α) := by
  have hu : constantCoeff (1 + α * β) = 1 := by simp [h]
  have hw : constantCoeff (1 + β * α) = 1 := by simp [h']
  have e : α * (1 + β * α) = (1 + α * β) * α := by noncomm_ring
  calc inv1 (1 + α * β) * α
      = inv1 (1 + α * β) * α * ((1 + β * α) * inv1 (1 + β * α)) := by
        rw [mul_inv1 hw, mul_one]
    _ = inv1 (1 + α * β) * (α * (1 + β * α)) * inv1 (1 + β * α) := by noncomm_ring
    _ = α * inv1 (1 + β * α) := by
        rw [e, ← mul_assoc, inv1_mul hu, one_mul]

/-- **The push-through identity for `τ`:** `τ(1 + αβ) = τ(1 + βα)`. -/
theorem tau₁_one_add_mul_comm {α β : PowerSeries R} (h : constantCoeff (α * β) = 0)
    (h' : constantCoeff (β * α) = 0) (m : ℕ) :
    tau₁ (1 + α * β) m = tau₁ (1 + β * α) m := by
  have push₁ := inv1_one_add_mul_mul h h'
  have push₂ := (inv1_one_add_mul_mul h' h).symm
  simp only [tau₁, degDeriv_add, degDeriv_mul, degDeriv_one, zero_add, mul_add, map_add]
  have t1 : qCoeff m (inv1 (1 + α * β) * (degDeriv α * β)) =
      qCoeff m (inv1 (1 + β * α) * (β * degDeriv α)) := by
    rw [← mul_assoc, qCoeff_mul_comm, ← mul_assoc, push₂, mul_assoc]
  have t2 : qCoeff m (inv1 (1 + α * β) * (α * degDeriv β)) =
      qCoeff m (inv1 (1 + β * α) * (degDeriv β * α)) := by
    rw [← mul_assoc, push₁, mul_assoc, qCoeff_mul_comm, mul_assoc]
  rw [t1, t2, add_comm]


/-! ### Elementary power series -/

/-- The power series over `M_n(R)` with entry `f` at `(i, j)` and zero elsewhere. -/
def entryPS (i j : n) (f : PowerSeries R) : PowerSeries (Matrix n n R) :=
  PowerSeries.mk fun m => Matrix.single i j (coeff m f)

/-- The `m`-th coefficient of `entryPS i j f` is `coeff m f` at `(i, j)` and zero elsewhere. -/
theorem coeff_entryPS (i j : n) (f : PowerSeries R) (m : ℕ) :
    coeff m (entryPS i j f) = Matrix.single i j (coeff m f) := coeff_mk _ _

/-- For `i ≠ j`, the product of two power series supported at `(i, j)` is zero. -/
theorem entryPS_mul_entryPS {i j : n} (hij : i ≠ j) (f g : PowerSeries R) :
    entryPS i j f * entryPS i j g = 0 := by
  ext m : 1
  rw [coeff_mul, map_zero]
  exact Finset.sum_eq_zero fun p _ => by
    rw [coeff_entryPS, coeff_entryPS]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _

/-- `T d/dT` commutes with `entryPS i j`. -/
theorem degDeriv_entryPS (i j : n) (f : PowerSeries R) :
    degDeriv (entryPS i j f) = entryPS i j (degDeriv f) := by
  ext m : 1
  simp [coeff_degDeriv, coeff_entryPS, Matrix.smul_single]

/-- For `i ≠ j`, every coefficient of `entryPS i j f` has trace zero. -/
theorem trCoeff_entryPS {i j : n} (hij : i ≠ j) (f : PowerSeries R) (m : ℕ) :
    trCoeff n m (entryPS i j f) = 0 := by
  simp [trCoeff_apply, trq_apply, coeff_entryPS, Matrix.trace_single_eq_of_ne _ _ _ hij]

/-- The elementary power series `1 + f E_ij`. -/
def elemPS (i j : n) (f : PowerSeries R) : PowerSeries (Matrix n n R) := 1 + entryPS i j f

/-- `1 + f E_ij` has constant coefficient `1` when `f` has constant coefficient `0`. -/
theorem constantCoeff_elemPS (i j : n) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (elemPS i j f) = 1 := by
  rw [elemPS, map_add, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_entryPS,
    coeff_zero_eq_constantCoeff_apply, hf, Matrix.single_zero, add_zero]

/-- For `i ≠ j`, the inverse of `1 + f E_ij` is `1 - f E_ij`. -/
theorem inv1_elemPS {i j : n} (hij : i ≠ j) {f : PowerSeries R} (hf : constantCoeff f = 0) :
    inv1 (elemPS i j f) = 1 - entryPS i j f := by
  refine inv1_eq_of_mul_eq_one (constantCoeff_elemPS i j hf) ?_
  rw [elemPS, add_mul, one_mul, mul_sub, mul_one, entryPS_mul_entryPS hij]
  abel

/-- **`τ` kills elementary power series.** -/
theorem tau_elemPS {i j : n} (hij : i ≠ j) {f : PowerSeries R} (hf : constantCoeff f = 0)
    (m : ℕ) : tau (elemPS i j f) m = 0 := by
  rw [tau, inv1_elemPS hij hf, elemPS, degDeriv_add, degDeriv_one, zero_add, degDeriv_entryPS,
    sub_mul, one_mul, entryPS_mul_entryPS hij, sub_zero, trCoeff_entryPS hij]

/-- In degree `m ≠ 0`, the coefficient of `1 + f E_ij` is `coeff m f` at `(i, j)`. -/
theorem coeff_elemPS_of_ne_zero (i j : n) (f : PowerSeries R) {m : ℕ} (hm : m ≠ 0) :
    coeff m (elemPS i j f) = Matrix.single i j (coeff m f) := by
  rw [elemPS, map_add, coeff_one, ite_eq_right hm, zero_add, coeff_entryPS]


/-! ### Power series congruent to `1` modulo `T ^ k` -/

section Window

variable {S : Type*} [Ring S]

/-- `z ≡ 1 (mod T ^ k)`: the constant coefficient is `1` and the coefficients in degrees
`0 < j < k` vanish. -/
def IsOneTo (z : PowerSeries S) (k : ℕ) : Prop :=
  constantCoeff z = 1 ∧ ∀ j, 0 < j → j < k → coeff j z = 0

/-- A power series congruent to `1` modulo `T ^ k` has zeroth coefficient `1`. -/
theorem IsOneTo.coeff_zero {z : PowerSeries S} {k : ℕ} (hz : IsOneTo z k) : coeff 0 z = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply]; exact hz.1

/-- For `0 < j`, the degree-`j` coefficient of `u * w` only involves the terms with a factor of
degree `0`, provided the products of the other coefficients vanish. -/
private theorem coeff_mul_eq_add_of_mul_eq_zero {u w : PowerSeries S} {j : ℕ} (hj : 0 < j)
    (h : ∀ a b, a + b = j → 0 < a → 0 < b → coeff a u * coeff b w = 0) :
    coeff j (u * w) = coeff 0 u * coeff j w + coeff j u * coeff 0 w := by
  rw [coeff_mul, Finset.sum_eq_add (0, j) (j, 0) (by simp; omega)]
  · intro c hc hne
    rw [Finset.mem_antidiagonal] at hc
    refine h c.1 c.2 hc (Nat.pos_of_ne_zero fun h0 => hne.1 (Prod.ext h0 (by omega)))
      (Nat.pos_of_ne_zero fun h0 => hne.2 (Prod.ext (by omega) h0))
  · intro h; simp at h
  · intro h; simp at h

/-- In the window `0 < j ≤ k`, the coefficients of a product of two power series congruent to `1`
modulo `T ^ k` add. -/
theorem coeff_mul_of_isOneTo {u w : PowerSeries S} {k : ℕ} (hu : IsOneTo u k) (hw : IsOneTo w k)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) : coeff j (u * w) = coeff j u + coeff j w := by
  rw [coeff_mul_eq_add_of_mul_eq_zero hj fun a b hab ha _ => by
    rw [hu.2 a ha (by omega), zero_mul], hu.coeff_zero, hw.coeff_zero, one_mul, mul_one, add_comm]

/-- Power series congruent to `1` modulo `T ^ k` are closed under multiplication. -/
theorem IsOneTo.mul {u w : PowerSeries S} {k : ℕ} (hu : IsOneTo u k) (hw : IsOneTo w k) :
    IsOneTo (u * w) k :=
  ⟨by simp [hu.1, hw.1], fun j hj hjk => by
    rw [coeff_mul_of_isOneTo hu hw hj hjk.le, hu.2 j hj hjk, hw.2 j hj hjk, add_zero]⟩

/-- If `v ≡ 1 (mod T ^ k)`, then `v⁻¹ ≡ 1 (mod T ^ k)`, and for `0 < k` the degree-`k`
coefficient of `v⁻¹` is the negative of that of `v`. -/
theorem IsOneTo.isOneTo_inv1 {v : PowerSeries S} {k : ℕ} (hv : IsOneTo v k) :
    IsOneTo (inv1 v) k ∧ (0 < k → coeff k (inv1 v) = -coeff k v) := by
  have hvw := mul_inv1 hv.1
  have key : ∀ j, 0 < j → j ≤ k → (∀ i, 0 < i → i < j → coeff i (inv1 v) = 0) →
      coeff j (inv1 v) = -coeff j v := by
    intro j hj hjk ih
    have h := congrArg (coeff j) hvw
    rw [coeff_one, ite_eq_right hj.ne', coeff_mul_eq_add_of_mul_eq_zero hj fun a b hab _ hb => by
      rw [ih b hb (by omega), mul_zero]] at h
    rw [hv.coeff_zero, one_mul, show coeff 0 (inv1 v) = 1 by
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv1], mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hlow : ∀ j, 0 < j → j < k → coeff j (inv1 v) = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hjk
      rw [key j hj hjk.le (fun i hi hij => ih i hij hi (by omega)), hv.2 j hj hjk, neg_zero]
  exact ⟨⟨constantCoeff_inv1 v, hlow⟩, fun hk => key k hk le_rfl fun i hi hik => hlow i hi hik⟩

/-- A product of power series congruent to `1` modulo `T ^ k` is congruent to `1` modulo
`T ^ k`, and for `0 < k` its degree-`k` coefficient is the sum of those of the factors. -/
theorem isOneTo_list_prod {k : ℕ} (L : List (PowerSeries S)) (hL : ∀ u ∈ L, IsOneTo u k) :
    IsOneTo L.prod k ∧ (0 < k → coeff k L.prod = (L.map (coeff k)).sum) := by
  induction L with
  | nil => exact ⟨⟨by simp, fun j hj _ => by simp [coeff_one, hj.ne']⟩, fun hk => by
      simp [coeff_one, hk.ne']⟩
  | cons u L ih =>
    have hu := hL u (by simp)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hL w (by simp [hw])
    refine ⟨by rw [List.prod_cons]; exact hu.mul ih1, fun hk => ?_⟩
    rw [List.prod_cons, coeff_mul_of_isOneTo hu ih1 hk le_rfl, ih2 hk, List.map_cons,
      List.sum_cons]

end Window

/-! ### The basic elements `1 + x T ^ k` and `1 - A T` -/

section Basic

variable {S : Type*} [Ring S]

/-- The coefficients of `1 + x T ^ k`. -/
theorem coeff_one_add_X_pow_mul_C (k m : ℕ) (x : S) :
    coeff m (1 + X ^ k * C x) = (if m = 0 then 1 else 0) + (if m = k then x else 0) := by
  rw [map_add, coeff_one, coeff_X_pow_mul', coeff_C]
  congr 1
  by_cases h : m = k
  · subst h; simp
  · by_cases h' : k ≤ m
    · rw [ite_eq_left h', ite_eq_right (by omega), ite_eq_right h]
    · rw [ite_eq_right h', ite_eq_right h]

/-- For `0 < k`, `1 + x T ^ k ≡ 1 (mod T ^ k)`. -/
theorem isOneTo_one_add_X_pow_mul_C {k : ℕ} (hk : 0 < k) (x : S) :
    IsOneTo (1 + X ^ k * C x) k := by
  refine ⟨?_, fun j hj hjk => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_one_add_X_pow_mul_C, ite_eq_left rfl,
      ite_eq_right (Ne.symm hk.ne'), add_zero]
  · rw [coeff_one_add_X_pow_mul_C, ite_eq_right hj.ne', ite_eq_right hjk.ne, add_zero]

/-- For `0 < k`, the degree-`k` coefficient of `1 + x T ^ k` is `x`. -/
theorem coeff_k_one_add_X_pow_mul_C {k : ℕ} (hk : 0 < k) (x : S) :
    coeff k (1 + X ^ k * C x) = x := by
  rw [coeff_one_add_X_pow_mul_C, ite_eq_right hk.ne', ite_eq_left rfl, zero_add]

/-- For `0 < k`, the constant coefficient of `1 + x T ^ k` is `1`. -/
theorem constantCoeff_one_add_X_pow_mul_C {k : ℕ} (hk : 0 < k) (x : S) :
    constantCoeff (1 + X ^ k * C x) = 1 := (isOneTo_one_add_X_pow_mul_C hk x).1

/-- The `m`-th coefficient of `T f` is `0` for `m = 0` and the `(m - 1)`-st coefficient of `f`
otherwise. -/
theorem coeff_X_mul_cases (m : ℕ) (f : PowerSeries S) :
    coeff m (X * f) = if m = 0 then 0 else coeff (m - 1) f := by
  rcases m with _ | m
  · simp
  · rw [coeff_succ_X_mul, ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]

/-- The geometric series inverts `1 - A T`. -/
theorem inv1_one_sub_X_mul_C (A : S) :
    inv1 (1 - X * C A) = PowerSeries.mk fun m => A ^ m := by
  refine inv1_eq_of_mul_eq_one (by simp) ?_
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_mk, mul_assoc, coeff_X_mul_cases, coeff_one]
  rcases m with _ | m
  · simp
  · rw [ite_eq_right (Nat.succ_ne_zero m), ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel,
      coeff_C_mul, coeff_mk, ← pow_succ', sub_self]

/-- `T d/dT (1 - A T) = -A T`. -/
theorem degDeriv_one_sub_X_mul_C (A : S) : degDeriv (1 - X * C A) = -(X * C A) := by
  ext m
  rw [coeff_degDeriv, map_sub, coeff_one, map_neg, coeff_X_mul_cases, coeff_C]
  rcases m with _ | m
  · simp
  · rw [ite_eq_right (Nat.succ_ne_zero m), ite_eq_right (Nat.succ_ne_zero m), zero_sub,
      Nat.add_sub_cancel]
    rcases m with _ | m
    · simp
    · simp

end Basic

/-- For `0 < m`, the `m`-th coefficient of `(∑ A ^ j T ^ j) · A T` is `A ^ m`. -/
theorem coeff_geom_mul_X_mul_C {S : Type*} [Ring S] (A : S) {m : ℕ} (hm : 0 < m) :
    coeff m ((PowerSeries.mk fun j => A ^ j) * (X * C A)) = A ^ m := by
  rw [← mul_assoc, show (PowerSeries.mk fun j => A ^ j) * X = X * PowerSeries.mk fun j => A ^ j
    from (commute_X _).eq, mul_assoc, coeff_X_mul_cases, ite_eq_right hm.ne', coeff_mul_C,
    coeff_mk, ← pow_succ, Nat.sub_add_cancel hm]

/-- **`τ(1 - A T) = -∑ [tr(A ^ m)] T ^ m`.** -/
theorem tau_one_sub_X_mul_C (A : Matrix n n R) {m : ℕ} (hm : 0 < m) :
    tau (1 - X * C A) m = -trq n (A ^ m) := by
  rw [tau, inv1_one_sub_X_mul_C, degDeriv_one_sub_X_mul_C, mul_neg, map_neg, trCoeff_apply,
    coeff_geom_mul_X_mul_C A hm]

/-! ### `τ₁` of the basic elements -/

/-- For `0 < k`, `τ₁(1 + a b T ^ k) = τ₁(1 + b a T ^ k)`. -/
theorem tau₁_one_add_X_pow_mul_C_mul_comm {k : ℕ} (hk : 0 < k) (a b : R) (m : ℕ) :
    tau₁ (1 + X ^ k * C (a * b)) m = tau₁ (1 + X ^ k * C (b * a)) m := by
  have h1 : (X ^ k * C a) * C b = X ^ k * C (a * b) := by rw [mul_assoc, ← map_mul]
  have h2 : C b * (X ^ k * C a) = X ^ k * C (b * a) := by
    rw [← mul_assoc, (commute_X_pow (C b) k).eq, mul_assoc, ← map_mul]
  have := tau₁_one_add_mul_comm (α := X ^ k * C a) (β := C b)
    (by simp [hk.ne']) (by simp [hk.ne']) m
  rwa [h1, h2] at this

/-- The inverse of `1 + t T ^ k`. -/
theorem inv1_one_add_X_pow_mul_C {k : ℕ} (hk : 0 < k) (t : R) :
    inv1 (1 + X ^ k * C t) = PowerSeries.mk fun m => if k ∣ m then (-t) ^ (m / k) else 0 := by
  refine inv1_eq_of_mul_eq_one (constantCoeff_one_add_X_pow_mul_C hk t) ?_
  ext m
  rw [add_mul, one_mul, map_add, coeff_mk, mul_assoc, coeff_X_pow_mul', coeff_C_mul, coeff_mk,
    coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Nat.not_le.2 hk]
  · rw [ite_eq_right hm.ne']
    by_cases hkm : k ∣ m
    · obtain ⟨j, rfl⟩ := hkm
      have hj : 0 < j := Nat.pos_of_ne_zero fun h => by simp [h] at hm
      rw [ite_eq_left ⟨j, rfl⟩, ite_eq_left (Nat.le_mul_of_pos_right k hj),
        ite_eq_left ⟨j - 1, by rw [Nat.mul_sub_one]⟩, Nat.mul_div_cancel_left _ hk,
        show (k * j - k) / k = j - 1 by rw [← Nat.mul_sub_one, Nat.mul_div_cancel_left _ hk]]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ', neg_mul, neg_add_cancel]
    · rw [ite_eq_right hkm]
      split_ifs with h1 h2
      · exact absurd (by have := Nat.dvd_add h2 (dvd_refl k); rwa [Nat.sub_add_cancel h1] at this)
          hkm
      · rw [mul_zero, zero_add]
      · rw [zero_add]

/-- **`τ₁(1 + t T ^ k) = 0`** when `k` kills the classes of the powers of `t`. -/
theorem tau₁_one_add_X_pow_mul_C_eq_zero {k : ℕ} (hk : 0 < k) {t : R}
    (ht : ∀ i, 0 < i → k • q R (t ^ i) = 0) (m : ℕ) : tau₁ (1 + X ^ k * C t) m = 0 := by
  have hD : degDeriv (1 + X ^ k * C t) = X ^ k * C (k • t) := by
    ext j
    rw [coeff_degDeriv, coeff_one_add_X_pow_mul_C, coeff_X_pow_mul', coeff_C]
    rcases Nat.lt_trichotomy j k with hjk | rfl | hjk
    · rw [ite_eq_right (Nat.not_le.2 hjk), ite_eq_right hjk.ne, add_zero]
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · simp
      · simp [h0.ne']
    · simp [hk.ne']
    · rw [ite_eq_left hjk.le, ite_eq_right (by omega), ite_eq_right hjk.ne',
        ite_eq_right (by omega), add_zero, smul_zero]
  rw [tau₁, hD, inv1_one_add_X_pow_mul_C hk, ← mul_assoc, (commute_X_pow _ k).eq, mul_assoc,
    qCoeff_apply, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
    split_ifs with h'
    · obtain ⟨i, hi⟩ := h'
      rw [mul_smul_comm, map_nsmul, neg_pow, hi, Nat.mul_div_cancel_left _ hk, mul_assoc,
        ← pow_succ]
      rcases neg_one_pow_eq_or R i with h1 | h1 <;> rw [h1]
      · rw [one_mul, ht (i + 1) (Nat.succ_pos i)]
      · rw [neg_one_mul, map_neg, smul_neg, ht (i + 1) (Nat.succ_pos i), neg_zero]
    · rw [zero_mul, map_zero]
  · exact map_zero _

/-! ### Cyclic matrices: the point side -/

section Cyclic

/-- The cyclic matrix of size `d + 1` with `g` in the corner: `e_j ↦ e_{j+1}` for `j < d` and
`e_d ↦ g e_0`. Its `(d + 1)`-st power is `g` times the identity; it is the Frobenius of a closed
point of degree `d + 1` acting on the induced module. -/
def cyclicMatrix (d : ℕ) (g : R) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j => if (i : ℕ) = j + 1 then 1 else if i = 0 ∧ j = Fin.last d then g else 0

/-- For `j < d`, column `j` of the cyclic matrix is the basis vector `e_{j+1}`. -/
theorem cyclicMatrix_apply_of_lt (d : ℕ) (g : R) (k j : Fin (d + 1)) (hj : (j : ℕ) < d) :
    cyclicMatrix d g k j = if (k : ℕ) = j + 1 then 1 else 0 := by
  simp only [cyclicMatrix, Matrix.of_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd (congrArg Fin.val h2.2) (by simp; omega)
  · rfl

/-- The last column of the cyclic matrix is `g e_0`. -/
theorem cyclicMatrix_apply_last (d : ℕ) (g : R) (k : Fin (d + 1)) :
    cyclicMatrix d g k (Fin.last d) = if k = 0 then g else 0 := by
  have h1 : ¬ (k : ℕ) = (Fin.last d : ℕ) + 1 := by
    have := k.isLt
    simp
    omega
  simp only [cyclicMatrix, Matrix.of_apply, ite_eq_right h1, and_true]

/-- The entries of the `m`-th power of the cyclic matrix: the `(i, j)` entry is
`g ^ ((j + m) / (d + 1))` if `(j + m) % (d + 1) = i`, and zero otherwise. -/
theorem cyclicMatrix_pow_apply (d : ℕ) (g : R) (m : ℕ) (i j : Fin (d + 1)) :
    (cyclicMatrix d g ^ m) i j =
      if ((j : ℕ) + m) % (d + 1) = i then g ^ (((j : ℕ) + m) / (d + 1)) else 0 := by
  induction m generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply, add_zero, Nat.mod_eq_of_lt j.isLt,
      Nat.div_eq_of_lt j.isLt, pow_zero]
    by_cases h : i = j
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Fin.ext h'.symm)]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hj : (j : ℕ) < d
    · rw [Finset.sum_eq_single ⟨j + 1, by omega⟩]
      · rw [ih, cyclicMatrix_apply_of_lt d g _ j hj, ite_eq_left rfl, mul_one,
          show ((j : ℕ) + 1 + m) = (j : ℕ) + (m + 1) by ring]
      · intro k _ hk
        rw [cyclicMatrix_apply_of_lt d g _ j hj,
          ite_eq_right (fun h => hk (Fin.ext (by simp; omega))), mul_zero]
      · simp
    · have hjd : j = Fin.last d := Fin.ext (by have := j.isLt; simp; omega)
      subst hjd
      rw [Finset.sum_eq_single 0]
      · rw [ih, cyclicMatrix_apply_last, ite_eq_left rfl]
        simp only [Fin.val_zero, zero_add, Fin.val_last]
        rw [show d + (m + 1) = m + 1 * (d + 1) by ring, Nat.add_mul_mod_self_right,
          Nat.add_mul_div_right _ _ (Nat.succ_pos d)]
        split_ifs
        · rw [pow_succ]
        · rw [zero_mul]
      · intro k _ hk
        rw [cyclicMatrix_apply_last, ite_eq_right hk, mul_zero]
      · simp

/-- The trace of the `m`-th power of the cyclic matrix of size `d + 1` is
`(d + 1) • g ^ (m / (d + 1))` if `d + 1` divides `m`, and zero otherwise. -/
theorem trace_cyclicMatrix_pow (d : ℕ) (g : R) (m : ℕ) :
    Matrix.trace (cyclicMatrix d g ^ m) =
      if (d + 1) ∣ m then (d + 1 : ℕ) • g ^ (m / (d + 1)) else 0 := by
  simp only [Matrix.trace, Matrix.diag, cyclicMatrix_pow_apply]
  by_cases hm : (d + 1) ∣ m
  · rw [ite_eq_left hm]
    obtain ⟨c, rfl⟩ := hm
    have : ∀ i : Fin (d + 1), ((i : ℕ) + (d + 1) * c) % (d + 1) = i ∧
        ((i : ℕ) + (d + 1) * c) / (d + 1) = c := fun i =>
      ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt],
        by rw [Nat.add_mul_div_left _ _ (Nat.succ_pos d), Nat.div_eq_of_lt i.isLt, zero_add]⟩
    simp only [this, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.mul_div_cancel_left _ (Nat.succ_pos d)]
  · rw [ite_eq_right hm]
    refine Finset.sum_eq_zero fun i _ => ite_eq_right fun h => hm ?_
    have h2 := Nat.div_add_mod ((i : ℕ) + m) (d + 1)
    rw [h] at h2
    exact ⟨(i + m) / (d + 1), by omega⟩

end Cyclic

/-! ### The determinant `δ(z) = det_Λ(φ(z))` -/

section Determinant

variable {Λ : Type v} [CommRing Λ] {r : ℕ} (φ : R →+* Matrix (Fin r) (Fin r) Λ)

/-- A ring map `R → M_r(Λ)` applied blockwise to a square matrix over `R`. The block index is the
second coordinate, as in `Matrix.blockDiagonal`. -/
def blockMap (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n R →+* Matrix (Fin r × n) (Fin r × n) Λ where
  toFun A := Matrix.of fun x y => φ (A x.2 y.2) x.1 y.1
  map_one' := by
    ext x y
    simp only [Matrix.of_apply, Matrix.one_apply]
    by_cases h : x.2 = y.2
    · rw [ite_eq_left h, map_one, Matrix.one_apply]
      by_cases h' : x.1 = y.1
      · rw [ite_eq_left h', ite_eq_left (Prod.ext h' h)]
      · rw [ite_eq_right h', ite_eq_right fun e => h' (congrArg Prod.fst e)]
    · rw [ite_eq_right h, map_zero, Matrix.zero_apply,
        ite_eq_right fun e => h (congrArg Prod.snd e)]
  map_mul' A B := by
    ext x y
    simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, Matrix.sum_apply, map_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  map_zero' := by
    ext x y
    simp
  map_add' A B := by
    ext x y
    simp

/-- A power series with matrix coefficients as a matrix of power series. -/
def toMatPS (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PowerSeries (Matrix ι ι Λ) →+* Matrix ι ι (PowerSeries Λ) where
  toFun f := Matrix.of fun a b => PowerSeries.mk fun m => coeff m f a b
  map_one' := by
    ext a b m
    simp only [Matrix.of_apply, coeff_mk, coeff_one, Matrix.one_apply]
    split_ifs <;> simp_all [Matrix.one_apply]
  map_mul' f g := by
    ext a b m
    simp only [Matrix.of_apply, coeff_mk, coeff_mul, Matrix.mul_apply, map_sum,
      Matrix.sum_apply]
    rw [Finset.sum_comm]
  map_zero' := by
    ext a b m
    simp
  map_add' f g := by
    ext a b m
    simp

/-- The `m`-th coefficient of the `(a, b)` entry of `toMatPS ι f` is the `(a, b)` entry of the
`m`-th coefficient of `f`. -/
theorem coeff_toMatPS (ι : Type*) [Fintype ι] [DecidableEq ι] (f : PowerSeries (Matrix ι ι Λ))
    (a b : ι) (m : ℕ) : coeff m (toMatPS ι f a b) = coeff m f a b := by
  simp [toMatPS]

/-- The determinant `δ(z) = det_Λ(φ(z))` of a power series over `M_n(R)`, as a power series over
`Λ`. -/
def delta (z : PowerSeries (Matrix n n R)) : PowerSeries Λ :=
  (toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) z)).det

/-- `δ` is multiplicative. -/
theorem delta_mul (z w : PowerSeries (Matrix n n R)) :
    delta φ (z * w) = delta φ z * delta φ w := by
  simp [delta, Matrix.det_mul]

/-- `δ(1) = 1`. -/
theorem delta_one : delta φ (1 : PowerSeries (Matrix n n R)) = 1 := by
  simp [delta]

/-- `δ(z⁻¹) δ(z) = 1`. -/
theorem delta_inv1 {z : PowerSeries (Matrix n n R)} (hz : constantCoeff z = 1) :
    delta φ (inv1 z) * delta φ z = 1 := by
  rw [← delta_mul, inv1_mul hz, delta_one]

/-- The determinant `δ₁(u) = det_Λ(φ(u))` of a power series over `R`. -/
def delta₁ (u : PowerSeries R) : PowerSeries Λ :=
  (toMatPS (Fin r) (PowerSeries.map φ u)).det

/-- `δ₁` is multiplicative. -/
theorem delta₁_mul (u w : PowerSeries R) : delta₁ φ (u * w) = delta₁ φ u * delta₁ φ w := by
  simp [delta₁, Matrix.det_mul]

/-- `δ₁(1) = 1`. -/
theorem delta₁_one : delta₁ φ (1 : PowerSeries R) = 1 := by
  simp [delta₁]

/-- `δ₁(u⁻¹) δ₁(u) = 1`. -/
theorem delta₁_inv1 {u : PowerSeries R} (hu : constantCoeff u = 1) :
    delta₁ φ (inv1 u) * delta₁ φ u = 1 := by
  rw [← delta₁_mul, inv1_mul hu, delta₁_one]

/-- Applying `φ` blockwise to `diagPS u` gives the block diagonal matrix of the `φ(u i)`. -/
theorem toMatPS_map_blockMap_diagPS (u : n → PowerSeries R) :
    toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) (diagPS u)) =
      Matrix.blockDiagonal fun i => toMatPS (Fin r) (PowerSeries.map φ (u i)) := by
  ext ⟨x, a⟩ ⟨y, b⟩ m
  rw [coeff_toMatPS, coeff_map, coeff_diagPS, Matrix.blockDiagonal_apply]
  by_cases h : a = b
  · subst h
    simp [blockMap, coeff_toMatPS, coeff_map]
  · simp [blockMap, h]

/-- **`δ` of a diagonal power series is the product of the `δ₁`'s of its entries.** -/
theorem delta_diagPS (u : n → PowerSeries R) : delta φ (diagPS u) = ∏ i, delta₁ φ (u i) := by
  rw [delta, toMatPS_map_blockMap_diagPS, Matrix.det_blockDiagonal]
  rfl

/-- **`δ` is `1` on elementary power series.** -/
theorem delta_elemPS {i j : n} (hij : i ≠ j) (f : PowerSeries R) :
    delta φ (elemPS i j f) = 1 := by
  let F := toMatPS (Fin r) (PowerSeries.map φ f)
  let U : Matrix (Fin r × n) (Fin r) (PowerSeries Λ) :=
    Matrix.of fun x y => if x.2 = i then F x.1 y else 0
  let W : Matrix (Fin r) (Fin r × n) (PowerSeries Λ) :=
    Matrix.of fun y x => if x.2 = j ∧ y = x.1 then 1 else 0
  have hUWdef : U * W = Matrix.of fun p q => if p.2 = i ∧ q.2 = j then F p.1 q.1 else 0 := by
    refine Matrix.ext fun p q => ?_
    simp only [U, W, Matrix.mul_apply, Matrix.of_apply]
    by_cases hp : p.2 = i
    · simp only [hp, ite_true]
      by_cases hq : q.2 = j
      · simp only [hq, true_and, ite_true]
        rw [Finset.sum_eq_single q.1]
        · simp
        · intro y _ hy
          simp only [ite_eq_right hy, mul_zero]
        · simp
      · simp [hq]
    · simp [hp]
  have hUW : toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) (elemPS i j f)) = 1 + U * W := by
    rw [elemPS, map_add, map_one, map_add, map_one, hUWdef]
    congr 1
    refine Matrix.ext fun p q => ?_
    ext m
    rw [coeff_toMatPS, coeff_map, coeff_entryPS]
    simp only [Matrix.of_apply, blockMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.single_apply]
    by_cases hp : p.2 = i <;> by_cases hq : q.2 = j
    · simp [hp, hq, F, coeff_toMatPS, coeff_map]
    · simp [hp, hq, Ne.symm hq]
    · simp [hp, hq, Ne.symm hp]
    · simp [hp, hq, Ne.symm hp]
  have hWU : W * U = 0 := by
    refine Matrix.ext fun y y' => ?_
    simp only [W, U, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x.2 = j
    · rw [ite_eq_right (show ¬ x.2 = i by rw [hx]; exact Ne.symm hij), mul_zero]
    · rw [ite_eq_right (fun h => hx h.1), zero_mul]
  rw [delta, hUW, Matrix.det_one_add_mul_comm, hWU, add_zero, Matrix.det_one]


/-- `x T ^ k`, as a matrix of power series, is `T ^ k` times the constant matrix `x`. -/
theorem toMatPS_X_pow_mul_C (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ)
    (x : Matrix ι ι Λ) :
    toMatPS ι (X ^ k * C x) = (X ^ k : PowerSeries Λ) • x.map (C (R := Λ)) := by
  refine Matrix.ext fun a b => ?_
  ext m
  rw [coeff_toMatPS, coeff_X_pow_mul', coeff_C, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    coeff_X_pow_mul', coeff_C]
  split_ifs <;> simp

/-- `δ₁(1 + x T ^ k) = det_Λ(1 + φ(x) T ^ k)`. -/
theorem delta₁_one_add_X_pow_mul_C (k : ℕ) (x : R) :
    delta₁ φ (1 + X ^ k * C x) =
      (1 + (X ^ k : PowerSeries Λ) • (φ x).map (C (R := Λ))).det := by
  rw [delta₁, map_add, map_one, map_mul, map_pow, map_X, map_C, map_add, map_one,
    toMatPS_X_pow_mul_C]

/-- **`δ₁(1 + a b T ^ k) = δ₁(1 + b a T ^ k)`**, by Sylvester's determinant identity. -/
theorem delta₁_one_add_mul_comm (k : ℕ) (a b : R) :
    delta₁ φ (1 + X ^ k * C (a * b)) = delta₁ φ (1 + X ^ k * C (b * a)) := by
  rw [delta₁_one_add_X_pow_mul_C, delta₁_one_add_X_pow_mul_C, map_mul, map_mul,
    Matrix.map_mul, Matrix.map_mul, ← Matrix.smul_mul, Matrix.det_one_add_mul_comm,
    Matrix.mul_smul]

/-- If `φ t = 0`, then `δ₁(1 + t T ^ k) = 1`. -/
theorem delta₁_one_add_X_pow_mul_C_of_map_eq_zero (k : ℕ) {t : R} (ht : φ t = 0) :
    delta₁ φ (1 + X ^ k * C t) = 1 := by
  rw [delta₁_one_add_X_pow_mul_C, ht, Matrix.map_zero _ (map_zero _), smul_zero, add_zero,
    Matrix.det_one]

/-- `δ(1 - A T) = det_Λ(1 - φ(A) T)`, the characteristic series of `φ(A)`. -/
theorem delta_one_sub_X_mul_C (A : Matrix n n R) :
    delta φ (1 - X * C A) =
      (1 - (X : PowerSeries Λ) • (blockMap φ n A).map (C (R := Λ))).det := by
  rw [delta, map_sub, map_one, map_mul, map_X, map_C, map_sub, map_one,
    show (X : PowerSeries (Matrix (Fin r × n) (Fin r × n) Λ)) * C (blockMap φ n A) =
      X ^ 1 * C (blockMap φ n A) by rw [pow_one], toMatPS_X_pow_mul_C, pow_one]

end Determinant

/-! ### Products of lists -/

section Lists

variable {Λ : Type v} [CommRing Λ] {r : ℕ} (φ : R →+* Matrix (Fin r) (Fin r) Λ)

/-- A product of power series with constant coefficient `1` has constant coefficient `1`. -/
private theorem constantCoeff_list_prod_of_forall {S : Type*} [Ring S] (L : List (PowerSeries S))
    (hL : ∀ u ∈ L, constantCoeff u = 1) : constantCoeff L.prod = 1 := by
  rw [map_list_prod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact hL w hw

/-- `τ` of a product of power series with constant coefficient `1` is the sum of their `τ`'s. -/
theorem tau_list_prod (L : List (PowerSeries (Matrix n n R)))
    (hL : ∀ u ∈ L, constantCoeff u = 1) (m : ℕ) :
    tau L.prod m = (L.map fun u => tau u m).sum := by
  induction L with
  | nil => simp [tau_one]
  | cons u L ih =>
    have hu := hL u (by simp)
    have hL' : ∀ w ∈ L, constantCoeff w = 1 := fun w hw => hL w (by simp [hw])
    have hP := constantCoeff_list_prod_of_forall L hL'
    rw [List.prod_cons, tau_mul hu hP, ih hL', List.map_cons, List.sum_cons]

/-- `δ` of a product is the product of the `δ`'s. -/
theorem delta_list_prod (L : List (PowerSeries (Matrix n n R))) :
    delta φ L.prod = (L.map (delta φ)).prod := by
  induction L with
  | nil => simp [delta_one]
  | cons u L ih => rw [List.prod_cons, delta_mul, ih, List.map_cons, List.prod_cons]

end Lists

section StepLemma

variable {Λ : Type v} [CommRing Λ] {r : ℕ} (φ : R →+* Matrix (Fin r) (Fin r) Λ)

/-- `τ₁` of a product of power series with constant coefficient `1` is the sum of their
`τ₁`'s. -/
theorem tau₁_list_prod (L : List (PowerSeries R)) (hL : ∀ u ∈ L, constantCoeff u = 1) (m : ℕ) :
    tau₁ L.prod m = (L.map fun u => tau₁ u m).sum := by
  induction L with
  | nil => simp [tau₁, degDeriv_one]
  | cons u L ih =>
    have hL' : ∀ w ∈ L, constantCoeff w = 1 := fun w hw => hL w (by simp [hw])
    have hP := constantCoeff_list_prod_of_forall L hL'
    rw [List.prod_cons, tau₁_mul (hL u (by simp)) hP, ih hL', List.map_cons, List.sum_cons]

/-- `δ₁` of a product is the product of the `δ₁`'s. -/
theorem delta₁_list_prod (L : List (PowerSeries R)) :
    delta₁ φ L.prod = (L.map (delta₁ φ)).prod := by
  induction L with
  | nil => simp [delta₁_one]
  | cons u L ih => rw [List.prod_cons, delta₁_mul, ih, List.map_cons, List.prod_cons]

/-- A product of power series with constant coefficient `1` has constant coefficient `1`. -/
theorem constantCoeff_list_prod {S : Type*} [Ring S] (L : List (PowerSeries S))
    (hL : ∀ u ∈ L, constantCoeff u = 1) : constantCoeff L.prod = 1 :=
  constantCoeff_list_prod_of_forall L hL

/-! ### The induction step -/

/-- **The torsion hypothesis `(H_N)`.** For `0 < k ≤ N`, every `s ∈ R` whose class in `R^♮` is
killed by `k` is a sum of commutators plus an element `t` killed by `φ` all of whose powers have
classes killed by `k`. -/
def TraceDetectionHypothesis (N : ℕ) : Prop :=
  ∀ k, 0 < k → k ≤ N → ∀ s : R, k • q R s = 0 →
    ∃ (J : ℕ) (a b : Fin J → R) (t : R), s = ∑ j, (a j * b j - b j * a j) + t ∧ φ t = 0 ∧
      ∀ i, 0 < i → k • q R (t ^ i) = 0

/-- If `u` has zeroth coefficient `1` and `w` vanishes in degrees below `k`, then `u * w` and `w`
have the same degree-`k` coefficient. -/
theorem coeff_mul_eq_of_lt {S : Type*} [Ring S] {u w : PowerSeries S} {k : ℕ}
    (hu : coeff 0 u = 1) (hw : ∀ j < k, coeff j w = 0) : coeff k (u * w) = coeff k w := by
  rw [coeff_mul, Finset.sum_eq_single (0, k)]
  · rw [hu, one_mul]
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    rw [hw p.2 (by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd (Prod.ext h (by omega)) hne
      · omega), mul_zero]
  · intro h; simp at h

/-- If `z ≡ 1 (mod T ^ k)`, the degree-`k` coefficient of `z⁻¹ · T dz/dT` is `k` times that of
`z`. -/
theorem coeff_inv1_mul_degDeriv {z : PowerSeries (Matrix n n R)} {k : ℕ} (hz : IsOneTo z k) :
    coeff k (inv1 z * degDeriv z) = k • coeff k z := by
  rw [coeff_mul_eq_of_lt (by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv1])
    (fun j hj => by
      rw [coeff_degDeriv]
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact zero_smul _ _
      · rw [hz.2 j h hj, smul_zero]), coeff_degDeriv]

/-- If every entry of `u` is congruent to `1` modulo `T ^ k`, so is `diagPS u`, and its degree-`k`
coefficient is the diagonal matrix of the entries' degree-`k` coefficients. -/
private theorem isOneTo_diagPS {u : n → PowerSeries R} {k : ℕ} (hu : ∀ i, IsOneTo (u i) k) :
    IsOneTo (diagPS u) k ∧ coeff k (diagPS u) = Matrix.diagonal fun i => coeff k (u i) := by
  refine ⟨⟨?_, fun j hj hjk => ?_⟩, coeff_diagPS u k⟩
  · rw [constantCoeff_diagPS]
    simp only [(hu _).1]
    exact Matrix.diagonal_one
  · rw [coeff_diagPS]
    simp only [(hu _).2 j hj hjk]
    exact Matrix.diagonal_zero

/-- **The induction step.** If `z ≡ 1 (mod T ^ k)` and `τ(z)` vanishes in degree `k`, there is `v`
with the same coefficients as `z` up to degree `k`, `δ(v) = 1` and `τ(v) = 0`. -/
theorem exists_step (i₀ : n) {N : ℕ} (H : TraceDetectionHypothesis φ N) {k : ℕ} (hk : 0 < k)
    (hkN : k ≤ N) {z : PowerSeries (Matrix n n R)} (hz : IsOneTo z k) (htau : tau z k = 0) :
    ∃ v : PowerSeries (Matrix n n R), IsOneTo v k ∧ coeff k v = coeff k z ∧
      delta φ v = 1 ∧ ∀ m, tau v m = 0 := by
  classical
  set Cm := coeff k z with hCm
  have hks : k • q R (Matrix.trace Cm) = 0 := by
    have := htau
    rw [tau, trCoeff_apply, coeff_inv1_mul_degDeriv hz, map_nsmul, trq_apply] at this
    exact this
  obtain ⟨J, a, b, t, hs, hφt, ht⟩ := H k hk hkN _ hks
  -- the factors
  let offL : List (PowerSeries (Matrix n n R)) :=
    ((Finset.univ.filter fun p : n × n => p.1 ≠ p.2).toList).map fun p =>
      elemPS p.1 p.2 (X ^ k * C (Cm p.1 p.2))
  let D1 : PowerSeries (Matrix n n R) := diagPS fun i => 1 + X ^ k * C (Cm i i)
  let PL : List (PowerSeries R) :=
    (Finset.univ : Finset n).toList.map fun i => 1 + X ^ k * C (Cm i i)
  let VL : List (PowerSeries R) := (List.finRange J).map fun j =>
    (1 + X ^ k * C (a j * b j)) * inv1 (1 + X ^ k * C (b j * a j))
  let V : PowerSeries R := VL.prod * (1 + X ^ k * C t)
  let W : PowerSeries R := V * inv1 PL.prod
  let D2 : PowerSeries (Matrix n n R) := diagPS fun i => if i = i₀ then W else 1
  -- basic facts
  have hk0 : ∀ x : R, constantCoeff (X ^ k * C x : PowerSeries R) = 0 := fun x => by
    simp [hk.ne']
  have helem : ∀ (i j : n) (c : R), IsOneTo (elemPS i j (X ^ k * C c)) k ∧
      coeff k (elemPS i j (X ^ k * C c)) = Matrix.single i j c := by
    intro i j c
    refine ⟨⟨constantCoeff_elemPS i j (hk0 c), fun j' hj' hj'k => ?_⟩, ?_⟩
    · rw [coeff_elemPS_of_ne_zero _ _ _ hj'.ne', coeff_X_pow_mul', ite_eq_right (by omega),
        Matrix.single_zero]
    · rw [coeff_elemPS_of_ne_zero _ _ _ hk.ne', coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
        coeff_zero_C]
  have hmemoff : ∀ u ∈ offL, ∃ p : n × n, p.1 ≠ p.2 ∧
      u = elemPS p.1 p.2 (X ^ k * C (Cm p.1 p.2)) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
    exact ⟨p, (Finset.mem_filter.1 (Finset.mem_toList.1 hp)).2, rfl⟩
  have hoffL : ∀ u ∈ offL, IsOneTo u k := fun u hu => by
    obtain ⟨p, -, rfl⟩ := hmemoff u hu
    exact (helem _ _ _).1
  obtain ⟨hoff1, hoff2⟩ := isOneTo_list_prod offL hoffL
  have hone : ∀ x : R, IsOneTo (1 + X ^ k * C x) k := fun x => isOneTo_one_add_X_pow_mul_C hk x
  have hVLm : ∀ u ∈ VL, IsOneTo u k := fun u hu => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hu
    exact (hone _).mul (hone _).isOneTo_inv1.1
  obtain ⟨hVL1, hVL2⟩ := isOneTo_list_prod VL hVLm
  have hPLm : ∀ u ∈ PL, IsOneTo u k := fun u hu => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
    exact hone _
  obtain ⟨hPL1, hPL2⟩ := isOneTo_list_prod PL hPLm
  have hV1 : IsOneTo V k := hVL1.mul (hone t)
  have hcoeffV : coeff k V = ∑ j, (a j * b j - b j * a j) + t := by
    rw [coeff_mul_of_isOneTo hVL1 (hone t) hk le_rfl, hVL2 hk, coeff_k_one_add_X_pow_mul_C hk,
      Fin.sum_univ_def, List.map_map]
    congr 2
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [coeff_mul_of_isOneTo (hone _) (hone _).isOneTo_inv1.1 hk le_rfl,
      (hone _).isOneTo_inv1.2 hk, coeff_k_one_add_X_pow_mul_C hk,
      coeff_k_one_add_X_pow_mul_C hk, sub_eq_add_neg]
  have hcoeffP : coeff k PL.prod = Matrix.trace Cm := by
    rw [hPL2 hk, List.map_map, Matrix.trace]
    rw [show (coeff k ∘ fun i => 1 + X ^ k * C (Cm i i)) = fun i => Cm i i from
      funext fun i => coeff_k_one_add_X_pow_mul_C hk _, Finset.sum_map_toList]
    rfl
  have hinvP := hPL1.isOneTo_inv1
  have hW1 : IsOneTo W k := hV1.mul hinvP.1
  have hcoeffW : coeff k W = 0 := by
    rw [coeff_mul_of_isOneTo hV1 hinvP.1 hk le_rfl, hinvP.2 hk, hcoeffV, hcoeffP, ← hs,
      add_neg_cancel]
  have hD1 : IsOneTo D1 k ∧ coeff k D1 = Matrix.diagonal fun i => Cm i i := by
    have := isOneTo_diagPS fun i => hone (Cm i i)
    simpa only [coeff_k_one_add_X_pow_mul_C hk] using this
  have hcW : ∀ i, IsOneTo (if i = i₀ then W else 1) k := fun i => by
    split_ifs
    · exact hW1
    · exact ⟨map_one _, fun j hj _ => by rw [coeff_one, ite_eq_right hj.ne']⟩
  have hD2 : IsOneTo D2 k ∧ coeff k D2 = 0 := by
    refine ⟨(isOneTo_diagPS hcW).1, ?_⟩
    rw [(isOneTo_diagPS hcW).2]
    have : ∀ i, coeff k (if i = i₀ then W else 1) = 0 := fun i => by
      split_ifs
      · exact hcoeffW
      · rw [coeff_one, ite_eq_right hk.ne']
    simp only [this]
    exact Matrix.diagonal_zero
  have hv1 : IsOneTo (offL.prod * D1 * D2) k := (hoff1.mul hD1.1).mul hD2.1
  refine ⟨offL.prod * D1 * D2, hv1, ?_, ?_, ?_⟩
  · -- the coefficient in degree `k`
    rw [coeff_mul_of_isOneTo (hoff1.mul hD1.1) hD2.1 hk le_rfl,
      coeff_mul_of_isOneTo hoff1 hD1.1 hk le_rfl, hoff2 hk, hD1.2, hD2.2, add_zero,
      List.map_map]
    have hfun : (coeff k ∘ fun p : n × n => elemPS p.1 p.2 (X ^ k * C (Cm p.1 p.2))) =
        fun p => Matrix.single p.1 p.2 (Cm p.1 p.2) := funext fun p => (helem _ _ _).2
    rw [hfun, Finset.sum_map_toList]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.add_apply, Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_zero, zero_add, ite_eq_left rfl]
      intro p hp
      rw [Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) (Finset.mem_filter.1 hp).2
      · rfl
    · rw [ite_eq_right hij, add_zero, Finset.sum_eq_single (i, j)]
      · rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]
      · intro p _ hp
        rw [Matrix.single_apply, ite_eq_right]
        rintro ⟨h1, h2⟩
        exact hp (Prod.ext h1 h2)
      · intro h
        exact absurd (by simp [hij]) h
  · -- `δ(v) = 1`
    have hδoff : delta φ offL.prod = 1 := by
      rw [delta_list_prod]
      exact List.prod_eq_one fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, hp, rfl⟩ := hmemoff u hu
        exact delta_elemPS φ hp _
    have hδV : delta₁ φ V = 1 := by
      rw [delta₁_mul, delta₁_list_prod, delta₁_one_add_X_pow_mul_C_of_map_eq_zero φ k hφt,
        mul_one]
      exact List.prod_eq_one fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hu
        rw [delta₁_mul, delta₁_one_add_mul_comm, mul_comm,
          delta₁_inv1 φ (constantCoeff_one_add_X_pow_mul_C hk _)]
    have hδP : delta₁ φ PL.prod = ∏ i, delta₁ φ (1 + X ^ k * C (Cm i i)) := by
      rw [delta₁_list_prod, List.map_map, Finset.prod_map_toList]
      rfl
    have hδD2 : delta φ D2 = delta₁ φ W := by
      rw [delta_diagPS]
      simp only [apply_ite (delta₁ φ), delta₁_one]
      rw [Finset.prod_ite_eq']
      simp
    rw [delta_mul, delta_mul, hδoff, one_mul, delta_diagPS, hδD2, delta₁_mul, hδV, one_mul,
      ← hδP, mul_comm, delta₁_inv1 φ hPL1.1]
  · -- `τ(v) = 0`
    intro m
    have hcoff : constantCoeff offL.prod = 1 := hoff1.1
    rw [tau_mul (hcoff.trans rfl ▸ (hoff1.mul hD1.1).1) hD2.1.1, tau_mul hcoff hD1.1.1]
    have hτoff : tau offL.prod m = 0 := by
      rw [tau_list_prod offL (fun u hu => (hoffL u hu).1)]
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, hp, rfl⟩ := hmemoff u hu
        exact tau_elemPS hp (hk0 _) m
    have hτD1 : tau D1 m = ∑ i, tau₁ (1 + X ^ k * C (Cm i i)) m :=
      tau_diagPS (fun i => (hone _).1) m
    have hτD2 : tau D2 m = tau₁ W m := by
      rw [tau_diagPS (fun i => (hcW i).1)]
      have h1 : tau₁ (1 : PowerSeries R) m = 0 := by simp [tau₁, degDeriv_one]
      simp only [apply_ite (fun u => tau₁ u m), h1]
      rw [Finset.sum_ite_eq']
      simp
    have hτV : tau₁ V m = 0 := by
      rw [tau₁_mul hVL1.1 (hone t).1, tau₁_list_prod VL (fun u hu => (hVLm u hu).1),
        tau₁_one_add_X_pow_mul_C_eq_zero hk ht, add_zero]
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hu
        rw [tau₁_mul (hone _).1 (constantCoeff_inv1 _), tau₁_inv1 (hone _).1,
          tau₁_one_add_X_pow_mul_C_mul_comm hk, add_neg_cancel]
    have hτP : tau₁ PL.prod m = ∑ i, tau₁ (1 + X ^ k * C (Cm i i)) m := by
      rw [tau₁_list_prod PL (fun u hu => (hPLm u hu).1), List.map_map, Finset.sum_map_toList]
      rfl
    rw [hτoff, hτD1, hτD2, tau₁_mul hV1.1 hinvP.1.1, hτV, tau₁_inv1 hPL1.1, hτP]
    abel

/-- `δ(z)` has constant coefficient `1` when `z` does. -/
theorem constantCoeff_delta {z : PowerSeries (Matrix n n R)} (hz : constantCoeff z = 1) :
    constantCoeff (delta φ z) = 1 := by
  rw [delta, RingHom.map_det]
  have : (constantCoeff (R := Λ)).mapMatrix
      (toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) z)) = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_toMatPS, coeff_map, coeff_zero_eq_constantCoeff_apply, hz, map_one]
  rw [this, Matrix.det_one]

/-- A power series over `M_n(R)` congruent to `1` modulo `T ^ (N + 1)` has `δ ≡ 1` modulo
`T ^ (N + 1)`. -/
theorem coeff_delta_of_isOneTo {N : ℕ} {z : PowerSeries (Matrix n n R)} (hz : IsOneTo z (N + 1))
    {j : ℕ} (hj : 0 < j) (hjN : j ≤ N) : coeff j (delta φ z) = 0 := by
  let I : Ideal (PowerSeries Λ) := Ideal.span {(X : PowerSeries Λ) ^ (N + 1)}
  let π := Ideal.Quotient.mk I
  have hM : π.mapMatrix (toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) z)) = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    have hmem : toMatPS (Fin r × n) (PowerSeries.map (blockMap φ n) z) a b -
        (1 : Matrix (Fin r × n) (Fin r × n) (PowerSeries Λ)) a b ∈ I := by
      rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, coeff_toMatPS, coeff_map, Matrix.one_apply, apply_ite (coeff m), coeff_one,
        map_zero]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [coeff_zero_eq_constantCoeff_apply, hz.1, map_one, Matrix.one_apply]
        split_ifs <;> simp_all
      · rw [hz.2 m hm0 hm, map_zero, Matrix.zero_apply, ite_eq_right hm0.ne']
        split_ifs <;> simp_all
    rw [Ideal.Quotient.eq.2 hmem, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : π (delta φ z) = 1 := by
    rw [delta, RingHom.map_det, hM, Matrix.det_one]
  have hdvd : (X : PowerSeries Λ) ^ (N + 1) ∣ delta φ z - 1 := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdet, map_one,
      sub_self]
  have := PowerSeries.X_pow_dvd_iff.1 hdvd j (by omega)
  rwa [map_sub, coeff_one, ite_eq_right hj.ne', sub_zero] at this

/-- **The Key Lemma.** Under the torsion hypothesis `(H_N)`, if `z ≡ 1 (mod T)` and its
logarithmic derivative `τ(z)` vanishes in degrees `1, …, N`, then `δ(z) ≡ 1 (mod T ^ (N + 1))`. -/
theorem coeff_delta_eq_zero_of_tau (i₀ : n) {N : ℕ} (H : TraceDetectionHypothesis φ N)
    {z : PowerSeries (Matrix n n R)} (hz : constantCoeff z = 1)
    (htau : ∀ m, 0 < m → m ≤ N → tau z m = 0) {j : ℕ} (hj : 0 < j) (hjN : j ≤ N) :
    coeff j (delta φ z) = 0 := by
  have key : ∀ k, 1 ≤ k → k ≤ N + 1 → ∃ z' : PowerSeries (Matrix n n R), IsOneTo z' k ∧
      delta φ z' = delta φ z ∧ ∀ m, tau z' m = tau z m := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => exact fun _ => ⟨z, ⟨hz, fun j hj hj1 => by omega⟩, rfl, fun _ => rfl⟩
    | succ k hk ih =>
      intro hkN
      obtain ⟨z', hz', hδ, hτ⟩ := ih (by omega)
      obtain ⟨v, hv, hvk, hδv, hτv⟩ := exists_step φ i₀ H hk (by omega) hz'
        (by rw [hτ k]; exact htau k hk (by omega))
      have hinv := hv.isOneTo_inv1
      refine ⟨inv1 v * z', ⟨?_, fun j hj hjk => ?_⟩, ?_, fun m => ?_⟩
      · exact (hinv.1.mul hz').1
      · rcases Nat.lt_or_ge j k with hjk' | hjk'
        · exact (hinv.1.mul hz').2 j hj hjk'
        · have : j = k := by omega
          subst this
          rw [coeff_mul_of_isOneTo hinv.1 hz' hj le_rfl, hinv.2 hj, hvk, neg_add_cancel]
      · rw [delta_mul, hδ]
        have := delta_inv1 φ hv.1
        rw [hδv, mul_one] at this
        rw [this, one_mul]
      · rw [tau_mul hinv.1.1 hz'.1, tau_inv1 hv.1, hτv, neg_zero, zero_add, hτ]
  obtain ⟨z', hz', hδ, -⟩ := key (N + 1) (by omega) le_rfl
  rw [← hδ]
  exact coeff_delta_of_isOneTo φ hz' hj hjN

/-- **Traces of powers detect the characteristic series up to `T ^ N`.** Let `A` and `B` be square
matrices over `R` with `[tr(A ^ m)] = [tr(B ^ m)]` in `R^♮` for `1 ≤ m ≤ N`. Under the torsion
hypothesis `(H_N)`, `det_Λ(1 - φ(A) T) ≡ det_Λ(1 - φ(B) T) (mod T ^ (N + 1))`. -/
theorem coeff_det_eq_of_trace_pow (i₀ : n) {N : ℕ} (H : TraceDetectionHypothesis φ N)
    (A B : Matrix n n R) (htr : ∀ m, 0 < m → m ≤ N → trq n (A ^ m) = trq n (B ^ m))
    {j : ℕ} (hjN : j ≤ N) :
    coeff j (1 - (X : PowerSeries Λ) • (blockMap φ n A).map (C (R := Λ))).det =
      coeff j (1 - (X : PowerSeries Λ) • (blockMap φ n B).map (C (R := Λ))).det := by
  have hA : constantCoeff (1 - X * C A : PowerSeries (Matrix n n R)) = 1 := by simp
  have hB : constantCoeff (1 - X * C B : PowerSeries (Matrix n n R)) = 1 := by simp
  set z := (1 - X * C A) * inv1 (1 - X * C B) with hzdef
  have hz : constantCoeff z = 1 := by simp [z, hA]
  have htz : ∀ m, 0 < m → m ≤ N → tau z m = 0 := by
    intro m hm hmN
    rw [tau_mul hA (constantCoeff_inv1 _), tau_inv1 hB, tau_one_sub_X_mul_C A hm,
      tau_one_sub_X_mul_C B hm, htr m hm hmN, neg_neg, neg_add_cancel]
  have hδz : ∀ j, 0 < j → j ≤ N → coeff j (delta φ z) = 0 := fun j hj hjN =>
    coeff_delta_eq_zero_of_tau φ i₀ H hz htz hj hjN
  have hrel : delta φ (1 - X * C A) = delta φ z * delta φ (1 - X * C B) := by
    rw [hzdef, delta_mul, mul_assoc, delta_inv1 φ hB, mul_one]
  rw [← delta_one_sub_X_mul_C, ← delta_one_sub_X_mul_C, hrel, coeff_mul]
  rw [Finset.sum_eq_single (0, j)]
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_delta φ hz, one_mul]
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    rw [hδz p.1 (by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd (Prod.ext h (by omega)) hne
      · exact h) (by omega), zero_mul]
  · intro h; simp at h

end StepLemma

end Stacks.CharSeriesTraceDetection
