module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Trace.Basic

/-!
# The pairing matrix annihilates the cokernel of a trace vector

Let `R` be a commutative ring, `S` an `R`-algebra, `τ : S →ₗ[R] R` any `R`-linear functional on
`S`, and `b : ι → S` a finite family. Pairing against the family gives an `R`-linear map

  `Φ : S ⟶ (ι → R)`, `s ↦ (τ (b i * s))ᵢ`,

and the determinant of the pairing matrix `(τ (b i * b j))ᵢⱼ` annihilates the cokernel of `Φ`.
This is formal: the family also gives a map back, `Ψ : (ι → R) ⟶ S`, `v ↦ ∑ v i • b i`, whose
composition with `Φ` is multiplication by the pairing matrix, and `M * adjugate M = det M • 1`.

Over an integrally closed base the functional `τ` of interest exists: if `R` is an integrally
closed domain with fraction field `K` and `L` is a finite extension of `K`, the field trace of an
element of `L` integral over `R` lies in `R`, so it defines an `R`-linear functional on the
integral closure of `R` in `L`. For a `K`-basis of `L` consisting of elements integral over `R`,
the determinant of the resulting pairing matrix is the discriminant of that basis, which is
nonzero when `L` is separable over `K`.

This is the algebraic content of the trace argument used for surfaces: a finite extension of
normal two-dimensional domains with separable fraction-field extension admits a map to a free
module whose cokernel is killed by one nonzero element of the base.

## Main definitions

* `Stacks.Trace.traceVector` is `Φ`.
* `Stacks.Trace.pairingMatrix` is the matrix `(τ (b i * b j))ᵢⱼ`.
* `Stacks.Trace.integralTrace` is the field trace of a finite extension, as an `R`-linear
  functional on the integral closure of an integrally closed domain `R`.

## Main results

* `Stacks.Trace.traceVector_linearCombination`: composing `Φ` with `Ψ` is multiplication by the
  pairing matrix.
* `Stacks.Trace.det_pairingMatrix_smul_mem_range`: the determinant of the pairing matrix carries
  every vector into the image of `Φ`.
* `Stacks.Trace.det_pairingMatrix_smul_eq_zero`: equivalently, it annihilates the cokernel.
* `Stacks.Trace.algebraMap_integralTrace`: the defining identity of `integralTrace`.
* `Stacks.Trace.algebraMap_det_pairingMatrix_integralTrace`: the determinant of the pairing
  matrix of an integral basis is the discriminant of that basis.
* `Stacks.Trace.det_pairingMatrix_integralTrace_ne_zero`: for a separable extension that
  determinant is nonzero.

## Implementation notes

The map back is Mathlib's `Fintype.linearCombination`, so only `Φ` and the matrix are new. The
core statements assume nothing whatever — no basis, no field, no finiteness of `S`, no
separability — because the argument is the adjugate identity and nothing else; every arithmetic
hypothesis enters only in the second half, where the functional is produced and its determinant
identified.

`integralTrace` is built by choosing, for each element, the preimage in `R` of its field trace;
the choice is unique because `algebraMap R K` is injective, which is also what makes the
resulting function additive and homogeneous. Its defining identity
`Stacks.Trace.algebraMap_integralTrace` is the only thing a consumer should need.

Mathlib's nearest statement, `Algebra.discr_mul_isIntegral_mem_adjoin`, is a different one: it is
specific to a `PowerBasis`, concludes membership in `Algebra.adjoin R` rather than in the image of
the pairing map, and goes through Cramer's rule in the field.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.Trace

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The formal core -/

/-- Pairing against a finite family `b` through a functional `τ`, as an `R`-linear map
`S ⟶ (ι → R)` sending `s` to `(τ (b i * s))ᵢ`. -/
def traceVector (τ : S →ₗ[R] R) (b : ι → S) : S →ₗ[R] (ι → R) where
  toFun s i := τ (b i * s)
  map_add' s t := by
    funext i
    simp [mul_add]
  map_smul' r s := by
    funext i
    simp [Algebra.mul_smul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- The `i`-th coordinate of `traceVector τ b s` is `τ (b i * s)`. -/
@[simp] lemma traceVector_apply (τ : S →ₗ[R] R) (b : ι → S) (s : S) (i : ι) :
    traceVector τ b s i = τ (b i * s) := rfl

/-- The matrix of the pairing of a finite family against itself through a functional. -/
def pairingMatrix (τ : S →ₗ[R] R) (b : ι → S) : Matrix ι ι R := fun i j => τ (b i * b j)

omit [Fintype ι] [DecidableEq ι] in
/-- The `(i, j)` entry of `pairingMatrix τ b` is `τ (b i * b j)`. -/
@[simp] lemma pairingMatrix_apply (τ : S →ₗ[R] R) (b : ι → S) (i j : ι) :
    pairingMatrix τ b i j = τ (b i * b j) := rfl

omit [DecidableEq ι] in
/-- **Pairing a linear combination of the family is multiplication by the pairing matrix.** -/
theorem traceVector_linearCombination (τ : S →ₗ[R] R) (b : ι → S) (v : ι → R) :
    traceVector τ b (Fintype.linearCombination R b v) = pairingMatrix τ b *ᵥ v := by
  funext i
  simp only [traceVector_apply, Fintype.linearCombination_apply, Finset.mul_sum,
    mulVec, dotProduct, pairingMatrix_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

/-- **The determinant of the pairing matrix carries every vector into the image of the pairing
map.** The preimage is the linear combination of the family with coefficients the adjugate of the
pairing matrix applied to the vector. -/
theorem det_pairingMatrix_smul_mem_range (τ : S →ₗ[R] R) (b : ι → S) (v : ι → R) :
    (pairingMatrix τ b).det • v ∈ LinearMap.range (traceVector τ b) := by
  refine ⟨Fintype.linearCombination R b ((pairingMatrix τ b).adjugate *ᵥ v), ?_⟩
  rw [traceVector_linearCombination, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

/-- **The determinant of the pairing matrix annihilates the cokernel of the pairing map.** -/
theorem det_pairingMatrix_smul_eq_zero (τ : S →ₗ[R] R) (b : ι → S)
    (z : (ι → R) ⧸ LinearMap.range (traceVector τ b)) :
    (pairingMatrix τ b).det • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H v =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact det_pairingMatrix_smul_mem_range τ b v

/-! ### The trace of an integral element over an integrally closed base -/

section Integral

variable (R) (K : Type*) {L : Type*} [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable [FiniteDimensional K L]

omit [IsDomain R] in
/-- The field trace of an element of `L` integral over `R` has a preimage in `R`. -/
theorem exists_algebraMap_eq_trace (x : integralClosure R L) :
    ∃ r : R, algebraMap R K r = Algebra.trace K L (x : L) :=
  (IsIntegrallyClosed.isIntegral_iff (K := K)).mp (Algebra.isIntegral_trace x.2)

/-- The field trace of an element of `L` integral over `R` lies in `R`, so the trace defines an
`R`-linear functional on the integral closure of `R` in `L`. -/
def integralTrace : integralClosure R L →ₗ[R] R where
  toFun x := (exists_algebraMap_eq_trace R K x).choose
  map_add' x y := IsFractionRing.injective R K <| by
    rw [map_add, (exists_algebraMap_eq_trace R K x).choose_spec,
      (exists_algebraMap_eq_trace R K y).choose_spec,
      (exists_algebraMap_eq_trace R K (x + y)).choose_spec]
    simp
  map_smul' r x := IsFractionRing.injective R K <| by
    have hsmul : ((r • x : integralClosure R L) : L) =
        algebraMap K L (algebraMap R K r) * (x : L) := by
      rw [← IsScalarTower.algebraMap_apply]
      simpa using Algebra.smul_def r (x : L)
    rw [RingHom.id_apply, smul_eq_mul, map_mul,
      (exists_algebraMap_eq_trace R K x).choose_spec,
      (exists_algebraMap_eq_trace R K (r • x)).choose_spec, hsmul, ← Algebra.smul_def,
      map_smul, smul_eq_mul]

omit [IsDomain R] in
/-- **The defining identity of `Stacks.Trace.integralTrace`:** it is a preimage in `R` of the
field trace. -/
@[simp] theorem algebraMap_integralTrace (x : integralClosure R L) :
    algebraMap R K (integralTrace R K x) = Algebra.trace K L (x : L) :=
  (exists_algebraMap_eq_trace R K x).choose_spec

omit [IsDomain R] in
/-- **The determinant of the pairing matrix of a basis of integral elements is the discriminant
of that basis.** -/
theorem algebraMap_det_pairingMatrix_integralTrace (b : Module.Basis ι K L)
    (hb : ∀ i, (b i) ∈ integralClosure R L) :
    algebraMap R K
        (pairingMatrix (integralTrace R K)
          (fun i => (⟨b i, hb i⟩ : integralClosure R L))).det = Algebra.discr K b := by
  rw [Algebra.discr_def, RingHom.map_det]
  congr 1
  funext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, pairingMatrix_apply,
    algebraMap_integralTrace, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    MulMemClass.coe_mul]

omit [IsDomain R] in
/-- **For a finite separable extension the determinant of the pairing matrix of a basis of
integral elements is nonzero.** -/
theorem det_pairingMatrix_integralTrace_ne_zero [Algebra.IsSeparable K L] (b : Module.Basis ι K L)
    (hb : ∀ i, (b i) ∈ integralClosure R L) :
    (pairingMatrix (integralTrace R K)
        (fun i => (⟨b i, hb i⟩ : integralClosure R L))).det ≠ 0 := by
  intro h
  refine Algebra.discr_not_zero_of_basis K b ?_
  rw [← algebraMap_det_pairingMatrix_integralTrace R K b hb, h, map_zero]

end Integral

end Stacks.Trace

end
