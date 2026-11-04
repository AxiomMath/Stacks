module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharSeriesTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Complex.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The traces of the powers determine the characteristic polynomial

Over a coefficient ring whose additive group is torsion free (for instance a field of
characteristic zero), the local factor `det(1 - A T)` of a square matrix is determined by the
traces of the powers of `A`: its logarithmic derivative is `-∑_{m ≥ 1} tr(A ^ m) T ^ m`
(`Stacks.EtaleCohomology.logDerivative_localCharSeries`), and a power series with constant
coefficient `1` is determined by its logarithmic derivative.  Over a field of characteristic zero
the characteristic polynomial is the reverse of `det(1 - A T)` once the size is known, so two
endomorphisms of finite-dimensional spaces of the same dimension with the same traces of all
powers have the same characteristic polynomial (Newton's identities).

In the cohomology of ℓ-adic sheaves the identifications of stalks and of Frobenius actions are
established at the level of traces, for all powers; this turns them into identifications of
characteristic polynomials.  In the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves it also turns real traces into
real characteristic polynomials (`ι`-realizability).

## Main results

* `Stacks.EtaleCohomology.localCharSeries_one_eq_of_trace_pow_eq`.
* `Stacks.EtaleCohomology.matrix_charpoly_eq_of_trace_pow_eq`.
* `Stacks.EtaleCohomology.charpoly_eq_of_trace_pow_eq`: the basis-free form.
* `Stacks.EtaleCohomology.coeff_charpoly_map_mem_range_ofReal_of_trace_pow`: if the
  traces of all powers are real along `ι`, so are the coefficients of the characteristic
  polynomial.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

section Matrix

variable {Λ : Type*} [CommRing Λ] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

/-- **The local factor `det(1 - A T)` is determined by the traces of the powers of `A`**, over a
coefficient ring with torsion-free additive group. -/
public theorem localCharSeries_one_eq_of_trace_pow_eq [IsAddTorsionFree Λ] (A : Matrix n n Λ)
    (B : Matrix m m Λ) (h : ∀ k : ℕ, 1 ≤ k → (A ^ k).trace = (B ^ k).trace) :
    localCharSeries A 1 = localCharSeries B 1 := by
  refine PowerSeries.eq_of_logDerivative_eq (constantCoeff_localCharSeries A one_ne_zero)
    (constantCoeff_localCharSeries B one_ne_zero) ?_
  rw [logDerivative_localCharSeries A one_ne_zero, logDerivative_localCharSeries B one_ne_zero]
  congr 2
  ext k
  simp only [coeff_traceSeries]
  split_ifs with hk
  · rw [Nat.div_one]
    exact h k (Nat.one_le_iff_ne_zero.2 hk.2)
  · rfl

/-- The polynomial local factor at a point of degree one is the reversed characteristic
polynomial. -/
public theorem localCharPolynomial_one_eq_charpolyRev (A : Matrix n n Λ) :
    localCharPolynomial A 1 = A.charpolyRev := by
  rw [localCharPolynomial, localCharPolyMatrix, pow_one, Matrix.charpolyRev]

/-- **Newton's identities, for matrices.**  Over a field of characteristic zero, two square
matrices of the same size whose powers have the same traces have the same characteristic
polynomial. -/
@[sga "7 IX 4.3" "partial"]
public theorem matrix_charpoly_eq_of_trace_pow_eq {K : Type*} [Field K] [CharZero K]
    (A : Matrix n n K) (B : Matrix m m K) (hcard : Fintype.card n = Fintype.card m)
    (h : ∀ k : ℕ, 1 ≤ k → (A ^ k).trace = (B ^ k).trace) : A.charpoly = B.charpoly := by
  have hs := localCharSeries_one_eq_of_trace_pow_eq A B h
  simp only [← coe_localCharPolynomial, localCharPolynomial_one_eq_charpolyRev] at hs
  have hrev : A.charpolyRev = B.charpolyRev := Polynomial.coe_inj.1 hs
  simp only [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
    hcard] at hrev
  have := congrArg (Polynomial.reflect (Fintype.card m)) hrev
  rwa [Polynomial.reflect_reflect, Polynomial.reflect_reflect] at this

end Matrix

section LinearMap

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The trace of a power of the matrix of an endomorphism is the trace of the power. -/
private theorem trace_toMatrix_pow {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F M) (f : Module.End F M) (k : ℕ) :
    ((LinearMap.toMatrix b b f) ^ k).trace = LinearMap.trace F M (f ^ k) := by
  rw [LinearMap.trace_eq_matrix_trace F b, LinearMap.toMatrix_pow]

/-- **Newton's identities.**  Over a field of characteristic zero, two endomorphisms of
finite-dimensional spaces of the same dimension whose powers have the same traces have the same
characteristic polynomial. -/
@[sga "7 IX 4.3" "partial"]
public theorem charpoly_eq_of_trace_pow_eq [CharZero K] (f : Module.End K V)
    (g : Module.End K W) (hdim : Module.finrank K V = Module.finrank K W)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = LinearMap.trace K W (g ^ k)) :
    f.charpoly = g.charpoly := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.charpoly_toMatrix f bV, ← LinearMap.charpoly_toMatrix g bW]
  refine matrix_charpoly_eq_of_trace_pow_eq _ _ (by simpa using hdim) fun k hk => ?_
  simp only [trace_toMatrix_pow]
  exact h k hk

/-- **Real traces give a real characteristic polynomial.**  If the traces of all powers of `f`
are real along `ι : K →+* ℂ`, so are the coefficients of the characteristic polynomial of `f`. -/
public theorem coeff_charpoly_map_mem_range_ofReal_of_trace_pow (ι : K →+* ℂ)
    (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → ι (LinearMap.trace K V (f ^ k)) ∈ Set.range ((↑) : ℝ → ℂ)) (j : ℕ) :
    ι (f.charpoly.coeff j) ∈ Set.range ((↑) : ℝ → ℂ) := by
  classical
  let b := Module.finBasis K V
  let A : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) ℂ :=
    (LinearMap.toMatrix b b f).map ι
  have htrA : ∀ k : ℕ, (A ^ k).trace = ι (LinearMap.trace K V (f ^ k)) := by
    intro k
    rw [← trace_toMatrix_pow b, AddMonoidHom.map_trace, Matrix.map_pow]
  have hA : ∀ k : ℕ, 1 ≤ k → ((A.map (starRingEnd ℂ)) ^ k).trace = (A ^ k).trace := by
    intro k hk
    rw [← Matrix.map_pow, ← AddMonoidHom.map_trace, htrA k]
    obtain ⟨r, hr⟩ := h k hk
    rw [← hr, Complex.conj_ofReal]
  have hc := matrix_charpoly_eq_of_trace_pow_eq _ _ rfl hA
  rw [Matrix.charpoly_map] at hc
  have hcf : (f.charpoly.map ι) = A.charpoly := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_map]
  have hj := congrArg (fun P => P.coeff j) hc
  simp only [Polynomial.coeff_map] at hj
  rw [← Polynomial.coeff_map, hcf]
  exact Complex.conj_eq_iff_real.1 hj |>.imp fun r hr => hr.symm

end LinearMap

end Stacks.EtaleCohomology

end
