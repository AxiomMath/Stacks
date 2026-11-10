module

public import StacksFrontier.NumberTheory.Padics.LAdicInvariantEigenvalue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerTensorComparison

/-!
# The exterior power as a tensor construction

A tensor construction `C` (`Stacks.LAdic.TensorConstruction`: a group homomorphism `R` with a Lie
algebra homomorphism `D`, `R = exp ∘ D ∘ log` near `1`) can be *compressed* by matrices `P`, `Q`
with `P Q = 1` and `‖P‖, ‖Q‖ ≤ 1` as soon as every `C.R g` preserves the kernel of `P`:
`g ↦ P (C.R g) Q`, `X ↦ P (C.D X) Q` is again a construction
(`Stacks.LAdic.TensorConstruction.compress`).  Applied to the `k`-th Kronecker power and to the
matrix `P` of `V^{⊗ k} → ⋀ᵏ V`, this exhibits `g ↦ ⋀ᵏ g` as a construction
(`Stacks.EtaleCohomology.exteriorConstruction`).

## Main definitions

* `Stacks.LAdic.TensorConstruction.compress`.
* `Stacks.EtaleCohomology.exteriorConstruction`.

## Main results

* `Stacks.LAdic.TensorConstruction.D_mem_stabilizer`: the derivative preserves the subspaces the
  group part preserves.
* `Stacks.EtaleCohomology.exteriorConstruction_R`: `(exteriorConstruction k).R g` is the compound
  matrix `⋀ᵏ g`, read in `Fin (card)`.

## References

* Kedlaya, *Fourier transforms and p-adic Weil II*, Proposition 6.1.6 (iii).
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix
open scoped Kronecker

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K]

variable {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

omit [CharZero K] [CompleteSpace K] [DecidableEq m] [DecidableEq p] in
/-- The sup norm of a product of rectangular matrices over an ultrametric field is at most the
product of the sup norms. -/
theorem norm_mul_le_of_ultrametric' {q : Type*} [Fintype q] (A : Matrix p m K) (B : Matrix m q K) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [norm_le_iff (by positivity)]
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le_entrywise_sup_norm A)
    (norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _))

namespace TensorConstruction

/-- The exponential of a small matrix, as a unit. -/
public def expUnit {X : Matrix n n K} (hX : ‖X‖ < (ℓ : ℝ)⁻¹) : (Matrix n n K)ˣ where
  val := exp X
  inv := exp (-X)
  val_inv := by
    have hX' : ‖-X‖ < (ℓ : ℝ)⁻¹ := by rwa [norm_neg]
    have h := exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) (Commute.neg_right (Commute.refl X))
      (mem_eball_expSeries hX) (mem_eball_expSeries hX')
    rw [add_neg_cancel, exp_zero] at h
    exact h.symm
  inv_val := by
    have hX' : ‖-X‖ < (ℓ : ℝ)⁻¹ := by rwa [norm_neg]
    have h := exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) (Commute.neg_left (Commute.refl X))
      (mem_eball_expSeries hX') (mem_eball_expSeries hX)
    rw [neg_add_cancel, exp_zero] at h
    exact h.symm

/-- **The derivative of a construction preserves the subspaces its group part preserves.** -/
public theorem D_mem_stabilizer (C : TensorConstruction ℓ K n m) {W : Submodule K (m → K)}
    (hW : ∀ g, (C.R g : Matrix m m K) ∈ stabilizerSubalgebra W) (X : Matrix n n K) :
    C.D X ∈ stabilizerSubalgebra W := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ((ℓ : ℝ)⁻¹) ^ j * ‖X‖ < (ℓ : ℝ)⁻¹ := by
    have h1 : ((ℓ : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hℓ
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hℓ0 (by positivity : (0 : ℝ) < ‖X‖ + 1)) h1
    refine ⟨j, ?_⟩
    calc ((ℓ : ℝ)⁻¹) ^ j * ‖X‖ ≤ ((ℓ : ℝ)⁻¹) ^ j * (‖X‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < (ℓ : ℝ)⁻¹ := (lt_div_iff₀ (by positivity)).1 hj
  set c : ℚ_[ℓ] := (ℓ : ℚ_[ℓ]) ^ j
  have hc : c ≠ 0 := pow_ne_zero _ ell_ne_zero
  have hcX : ‖c • X‖ < (ℓ : ℝ)⁻¹ := by rwa [norm_smul, norm_ell_pow]
  set g := expUnit hcX
  have hg : ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ := (norm_exp_sub_one_le hcX).trans_lt hcX
  have hlog : ladicLog ℓ (g : Matrix n n K) = c • X := ladicLog_exp hcX
  have hRg : (C.R g : Matrix m m K) = exp (C.D (c • X)) := by rw [C.map_eq g hg, hlog]
  have hDn : ‖C.D (c • X)‖ < (ℓ : ℝ)⁻¹ := C.norm_lt _ hcX
  have hRg1 : ‖(C.R g : Matrix m m K) - 1‖ < (ℓ : ℝ)⁻¹ := by
    rw [hRg]; exact (norm_exp_sub_one_le hDn).trans_lt hDn
  have hmem0 := (ladicLog_mem_stabilizerSubalgebra_iff hRg1).mpr (hW g)
  have hmem : C.D (c • X) ∈ stabilizerSubalgebra W := by
    have e : ladicLog ℓ (C.R g : Matrix m m K) = C.D (c • X) := by
      rw [hRg]; exact ladicLog_exp hDn
    rwa [e] at hmem0
  have hsmul : C.D (c • X) = (algebraMap ℚ_[ℓ] K c) • C.D X := by
    rw [← algebraMap_smul K c X]
    exact C.D.map_smul _ _
  rw [hsmul] at hmem
  have hc' : algebraMap ℚ_[ℓ] K c ≠ 0 := (map_ne_zero _).mpr hc
  have := (stabilizerSubalgebra W).smul_mem hmem (algebraMap ℚ_[ℓ] K c)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K]
  [DecidableEq m] [DecidableEq p] [Fintype p] in
/-- Two matrices with the same action on vectors are equal. -/
theorem ext_of_mulVec {A B : Matrix p m K} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  classical
  ext i j
  simpa [mulVec_single_one] using congrFun (h (Pi.single j 1)) i

section Compress

variable {P : Matrix p m K} {Q : Matrix m p K}

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- For `M` preserving the kernel of `P` (with `P Q = 1`), `P M (Q P) = P M`. -/
theorem mul_mul_mul_self_of_mem (hPQ : P * Q = 1) {M : Matrix m m K}
    (hM : M ∈ stabilizerSubalgebra (LinearMap.ker P.mulVecLin)) : P * M * (Q * P) = P * M := by
  refine ext_of_mulVec fun v => ?_
  have hw : Q *ᵥ (P *ᵥ v) - v ∈ LinearMap.ker P.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec, sub_self]
  have h := hM _ hw
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_sub,
    sub_eq_zero] at h
  simpa only [← Matrix.mulVec_mulVec] using h

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- For `M` preserving the kernel of `P` (with `P Q = 1`), compression by `P`, `Q` is
multiplicative on `M`, `M'`. -/
theorem compress_mul (hPQ : P * Q = 1) {M M' : Matrix m m K}
    (hM' : M ∈ stabilizerSubalgebra (LinearMap.ker P.mulVecLin)) :
    P * M * Q * (P * M' * Q) = P * (M * M') * Q := by
  calc P * M * Q * (P * M' * Q) = P * M * (Q * P) * M' * Q := by simp only [Matrix.mul_assoc]
    _ = P * (M * M') * Q := by rw [mul_mul_mul_self_of_mem hPQ hM']; simp only [Matrix.mul_assoc]

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- For `M` preserving the kernel of `P` (with `P Q = 1`), `(P M Q) ^ j = P M ^ j Q`. -/
theorem compress_pow (hPQ : P * Q = 1) {M : Matrix m m K}
    (hM : M ∈ stabilizerSubalgebra (LinearMap.ker P.mulVecLin)) (j : ℕ) :
    (P * M * Q) ^ j = P * M ^ j * Q := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPQ]
  | succ j ih =>
    rw [pow_succ, ih, compress_mul hPQ (Subalgebra.pow_mem _ hM j), pow_succ]

omit [CharZero K] in
/-- For `M` preserving the kernel of `P` (with `P Q = 1`) and `M`, `P M Q` small,
`exp (P M Q) = P (exp M) Q`. -/
theorem exp_compress (hPQ : P * Q = 1) {M : Matrix m m K}
    (hM : M ∈ stabilizerSubalgebra (LinearMap.ker P.mulVecLin)) (hMn : ‖M‖ < (ℓ : ℝ)⁻¹)
    (hPMQ : ‖P * M * Q‖ < (ℓ : ℝ)⁻¹) : exp (P * M * Q) = P * exp M * Q := by
  let Φ : Matrix m m K →+ Matrix p p K :=
    { toFun := fun X => P * X * Q
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hΦ : Continuous Φ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 := (hasSum_exp (ℓ := ℓ) hMn).map Φ hΦ
  have h2 := hasSum_exp (ℓ := ℓ) hPMQ
  have e : (Φ ∘ fun j : ℕ => (((j.factorial : ℕ) : ℚ_[ℓ])⁻¹) • M ^ j) =
      fun j => (((j.factorial : ℕ) : ℚ_[ℓ])⁻¹) • (P * M * Q) ^ j := by
    funext j
    simp only [Function.comp_apply, Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, compress_pow hPQ hM,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [e] at h1
  exact h2.unique h1

variable (C : TensorConstruction ℓ K n m) (hPQ : P * Q = 1)
  (hker : ∀ g, (C.R g : Matrix m m K) ∈ stabilizerSubalgebra (LinearMap.ker P.mulVecLin))
  (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)

omit [CharZero K] [CompleteSpace K] in
include hPQ hker in
/-- Compression of the group part of `C` by `P`, `Q` is multiplicative. -/
theorem compress_R_mul (g h : (Matrix n n K)ˣ) :
    P * (C.R g : Matrix m m K) * Q * (P * (C.R h : Matrix m m K) * Q) =
      P * (C.R (g * h) : Matrix m m K) * Q := by
  rw [compress_mul hPQ (hker g), map_mul, Units.val_mul]

include hP hQ in
/-- **The compression of a construction** by `P`, `Q` with `P Q = 1`, `‖P‖, ‖Q‖ ≤ 1`, when the
group part preserves the kernel of `P`: `g ↦ P (C.R g) Q`, `X ↦ P (C.D X) Q`. -/
public def compress : TensorConstruction ℓ K n p where
  R :=
    { toFun := fun g => ⟨P * (C.R g : Matrix m m K) * Q, P * (C.R g⁻¹ : Matrix m m K) * Q,
          by rw [compress_R_mul C hPQ hker, mul_inv_cancel, map_one, Units.val_one,
            Matrix.mul_one, hPQ],
          by rw [compress_R_mul C hPQ hker, inv_mul_cancel, map_one, Units.val_one,
            Matrix.mul_one, hPQ]⟩
      map_one' := by
        ext1
        change P * (C.R 1 : Matrix m m K) * Q = 1
        rw [map_one, Units.val_one, Matrix.mul_one, hPQ]
      map_mul' := fun g h => by
        ext1
        exact (compress_R_mul C hPQ hker g h).symm }
  D :=
    { toFun := fun X => P * C.D X * Q
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul]
      map_lie' := fun {X Y} => by
        have hX := C.D_mem_stabilizer hker X
        have hY := C.D_mem_stabilizer hker Y
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket,
          LieRing.of_associative_ring_bracket, compress_mul hPQ hX, compress_mul hPQ hY,
          Matrix.mul_sub, Matrix.sub_mul] }
  norm_lt X hX := by
    change ‖P * C.D X * Q‖ < _
    refine lt_of_le_of_lt ?_ (C.norm_lt X hX)
    calc ‖P * C.D X * Q‖ ≤ ‖P * C.D X‖ * ‖Q‖ := norm_mul_le_of_ultrametric' _ _
      _ ≤ (‖P‖ * ‖C.D X‖) * ‖Q‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le_of_ultrametric' _ _) (norm_nonneg _)
      _ ≤ 1 * ‖C.D X‖ * 1 := by gcongr
      _ = ‖C.D X‖ := by ring
  map_eq g hg := by
    change P * (C.R g : Matrix m m K) * Q = exp (P * C.D (ladicLog ℓ (g : Matrix n n K)) * Q)
    have hL : ‖ladicLog ℓ (g : Matrix n n K)‖ < (ℓ : ℝ)⁻¹ :=
      (norm_ladicLog_le hg.le).trans_lt hg
    have hDn := C.norm_lt _ hL
    have hPDQ : ‖P * C.D (ladicLog ℓ (g : Matrix n n K)) * Q‖ < (ℓ : ℝ)⁻¹ := by
      refine lt_of_le_of_lt ?_ hDn
      calc _ ≤ ‖P * C.D (ladicLog ℓ (g : Matrix n n K))‖ * ‖Q‖ := norm_mul_le_of_ultrametric' _ _
        _ ≤ (‖P‖ * ‖C.D (ladicLog ℓ (g : Matrix n n K))‖) * ‖Q‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le_of_ultrametric' _ _) (norm_nonneg _)
        _ ≤ 1 * ‖C.D (ladicLog ℓ (g : Matrix n n K))‖ * 1 := by gcongr
        _ = _ := by ring
    rw [exp_compress hPQ (C.D_mem_stabilizer hker _) hDn hPDQ, C.map_eq g hg]

/-- The group part of `C.compress` is `g ↦ P (C.R g) Q`. -/
public theorem compress_R_apply (g : (Matrix n n K)ˣ) :
    ((C.compress hPQ hker hP hQ).R g : Matrix p p K) = P * (C.R g : Matrix m m K) * Q :=
  rfl

end Compress

end TensorConstruction

end Stacks.LAdic

namespace Stacks.EtaleCohomology

open Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K]

variable {n : Type*} [Fintype n] [DecidableEq n] {r : ℕ} (k : ℕ)

omit [CharZero K] in
/-- The group part of a Kronecker power construction is the Kronecker power. -/
public theorem kronPow_R_eq {s : ℕ} (C : TensorConstruction ℓ K n (Fin s)) (j : ℕ)
    (g : (Matrix n n K)ˣ) :
    ((C.kronPow j).R g : Matrix (Fin (s ^ j)) (Fin (s ^ j)) K) =
      kronPowMatrix (C.R g : Matrix (Fin s) (Fin s) K) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [TensorConstruction.kronPow_R_succ, ih]
    rfl

/-- The image of an integer in a normed `ℚ_[ℓ]`-algebra has norm at most `1`. -/
theorem norm_intCast_le_one' (ℓ : ℕ) [Fact ℓ.Prime] {L : Type*} [NontriviallyNormedField L]
    [NormedAlgebra ℚ_[ℓ] L] (z : ℤ) : ‖(z : L)‖ ≤ 1 := by
  have h : (z : L) = algebraMap ℚ_[ℓ] L (z : ℚ_[ℓ]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_int_le_one _

/-- The matrix of `V^{⊗ k} → ⋀ᵏ V` has sup norm at most `1` over a normed `ℚ_[ℓ]`-algebra. -/
theorem norm_exteriorProjection_le (ℓ : ℕ) [Fact ℓ.Prime] {L : Type*} [NontriviallyNormedField L]
    [NormedAlgebra ℚ_[ℓ] L] : ‖exteriorProjection L r k‖ ≤ 1 := by
  rw [norm_le_iff zero_le_one]
  intro S I
  rw [exteriorProjection_apply]
  exact norm_intCast_le_one' ℓ _

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- The right inverse `exteriorSection K r k` of the matrix of `V^{⊗ k} → ⋀ᵏ V` has sup norm at
most `1`. -/
theorem norm_exteriorSection_le : ‖exteriorSection K r k‖ ≤ 1 := by
  rw [norm_le_iff zero_le_one]
  intro I S
  simp only [exteriorSection]
  split_ifs <;> simp

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- The `k`-th Kronecker power of a matrix preserves the kernel of `exteriorProjection K r k`. -/
theorem kronPowMatrix_mem_stabilizer (A : Matrix (Fin r) (Fin r) K) :
    kronPowMatrix A k ∈
      stabilizerSubalgebra (LinearMap.ker (exteriorProjection K r k).mulVecLin) := by
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
  rw [Matrix.mulVec_mulVec, exteriorProjection_mul_kronPowMatrix, ← Matrix.mulVec_mulVec, hx,
    Matrix.mulVec_zero]

/-- **The exterior power `g ↦ ⋀ᵏ g` as a tensor construction**, read on `Fin (card)` as
`Stacks.EtaleCohomology.exteriorPowerRepresentation` is: the compression of the `k`-th Kronecker
power by the matrix of `V^{⊗ k} → ⋀ᵏ V` and its right inverse. -/
public def exteriorConstruction :
    TensorConstruction ℓ K (Fin r) (Fin (Fintype.card (Set.powersetCard (Fin r) k))) :=
  (((TensorConstruction.id : TensorConstruction ℓ K (Fin r) (Fin r)).kronPow k).compress
    exteriorProjection_mul_exteriorSection
    (fun g => by
      rw [kronPow_R_eq]
      exact kronPowMatrix_mem_stabilizer k _)
    (norm_exteriorProjection_le k ℓ) (norm_exteriorSection_le k)).reindex
    (Fintype.equivFin _)

/-- **The group part of the exterior construction is the compound matrix.** -/
public theorem exteriorConstruction_R (g : (Matrix (Fin r) (Fin r) K)ˣ) :
    ((exteriorConstruction (ℓ := ℓ) k).R g : Matrix _ _ K) =
      Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
        (compoundMonoidHom k (g : Matrix (Fin r) (Fin r) K)) := by
  rw [exteriorConstruction, TensorConstruction.reindex_R_apply, TensorConstruction.compress_R_apply,
    kronPow_R_eq]
  change Matrix.reindex _ _
    (exteriorProjection K r k * kronPowMatrix (g : Matrix (Fin r) (Fin r) K) k *
      exteriorSection K r k) = _
  rw [exteriorProjection_mul_kronPowMatrix, Matrix.mul_assoc,
    exteriorProjection_mul_exteriorSection, Matrix.mul_one]

end Stacks.EtaleCohomology

end
