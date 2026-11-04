module

public import StacksFrontier.NumberTheory.Padics.LAdicGroupMonodromy
public import Mathlib.Algebra.Lie.Matrix

/-!
# Frobenius on invariant lines of tensor constructions, and Kronecker powers

In the situation of `Stacks.LAdic.TensorConstruction.norm_pow_mem_Icc_of_invariant`, a vector
`v` fixed by `C.R G` on which `C.R u` acts by `λ` is an eigenvector of `C.R z`, `z = exp B`,
with eigenvalue exactly `λ ^ ℓ ^ N`: the line `K v` is stable under `C.R G` and `C.R u`, and the
determinant of `C.R u ^ ℓ ^ N` on it is that of `C.R z`.  This sharpens the eigenvalue bound of
`norm_pow_mem_Icc_of_invariant` to an identity, which is what is needed when `v` lies in a
summand of the construction (an exterior power inside a tensor power) on which the eigenvalues of
`C.R z` are better controlled than on the whole construction.

The Kronecker powers `V ↦ V^{⊗ j}` of a construction are constructions
(`Stacks.LAdic.TensorConstruction.kronPow`), starting from the trivial one-dimensional
construction `Stacks.LAdic.TensorConstruction.unit`.

## Main results

* `Stacks.LAdic.TensorConstruction.mulVec_eq_of_invariant`.
* `Stacks.LAdic.TensorConstruction.reindex`, `Stacks.LAdic.TensorConstruction.kronPow`,
  `Stacks.LAdic.TensorConstruction.kronPow_R_succ`.
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

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

namespace TensorConstruction

/-- **The eigenvalue of `C.R z` on an invariant line.**  Let `v ≠ 0` be fixed by `C.R G` with
`C.R u v = λ v`.  Then `C.R z v = λ ^ ℓ ^ N v`, for `z = exp B` from the decomposition
`u ^ ℓ ^ N = exp A * exp B`. -/
public theorem mulVec_eq_of_invariant [IsAlgClosed K] (C : TensorConstruction ℓ K n m)
    {G : Subgroup (Matrix n n K)ˣ} (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    {u : (Matrix n n K)ˣ} (hu : ‖(u : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ}
    {A B : Matrix n n K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G)
    (hAn : ‖A‖ < (ℓ : ℝ)⁻¹) (hBn : ‖B‖ < (ℓ : ℝ)⁻¹)
    (hBG : ∀ g ∈ G, Commute B (g : Matrix n n K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (u : Matrix n n K) = A + B)
    {z : (Matrix n n K)ˣ} (hz : (z : Matrix n n K) = exp B) {v : m → K} (hv : v ≠ 0)
    (hGv : ∀ g ∈ G, (C.R g : Matrix m m K) *ᵥ v = v) {lam : K}
    (huv : (C.R u : Matrix m m K) *ᵥ v = lam • v) :
    (C.R z : Matrix m m K) *ᵥ v = lam ^ (ℓ ^ N) • v := by
  have hGW : ∀ g ∈ G, (C.R g : Matrix m m K) ∈ stabilizerSubalgebra (K ∙ v) := by
    intro g hg w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hGv g hg]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have huW : (C.R u : Matrix m m K) ∈ stabilizerSubalgebra (K ∙ v) := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, huv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hdetW : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ ∀ hg : (C.R g : Matrix m m K) ∈
      stabilizerSubalgebra (K ∙ v), LinearMap.det (stabRestrict (C.R g : Matrix m m K) hg) ^ k =
        1 := fun g hg => ⟨1, one_pos, fun hg' => by
    rw [det_stabRestrict_span_singleton hv (by rw [hGv g hg, one_smul]) hg', one_pow]⟩
  have hpow : ∀ j : ℕ, (C.R u : Matrix m m K) ^ j *ᵥ v = lam ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← Matrix.mulVec_mulVec, huv, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨-, hz', hu'', hdet⟩ := det_stabRestrict_construction hG C.R C.D C.norm_lt C.map_eq hu hA
    hAn hBn hBG hAB hsum hGW huW hdetW
  have hz1 : ‖(z : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ := by
    rw [hz]; exact (norm_exp_sub_one_le hBn).trans_lt hBn
  have hRz : (C.R z : Matrix m m K) = exp (C.D B) := by
    rw [C.map_eq z hz1, hz]
    exact congrArg (fun X => exp (C.D X)) (ladicLog_exp hBn)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hz' v (Submodule.mem_span_singleton_self v))
  rw [det_stabRestrict_span_singleton hv (hpow _) hu'',
    det_stabRestrict_span_singleton hv hc.symm hz'] at hdet
  rw [hRz, ← hc, hdet]

/-- The trivial one-dimensional construction `V ↦ K`. -/
public def unit : TensorConstruction ℓ K n (Fin 1) where
  R := 1
  D := 0
  norm_lt X _ := by
    change ‖(0 : Matrix (Fin 1) (Fin 1) K)‖ < _
    rw [norm_zero]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : ℓ.Prime).pos)
  map_eq g _ := by
    change (1 : Matrix (Fin 1) (Fin 1) K) = exp (0 : Matrix (Fin 1) (Fin 1) K)
    rw [exp_zero]

omit [CharZero K] [CompleteSpace K] in
/-- Reindexing a matrix along `e : m ≃ p` does not increase its (entrywise sup) norm. -/
theorem norm_reindex_le {p : Type*} [Fintype p] (e : m ≃ p) (M : Matrix m m K) :
    ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  rw [norm_le_iff (norm_nonneg _)]
  intro i j
  exact norm_entry_le_entrywise_sup_norm M

omit [CharZero K] in
/-- Reindexing matrices along `e : m ≃ p` is continuous. -/
theorem continuous_reindexAlgEquiv {p : Type*} [Fintype p] [DecidableEq p] (e : m ≃ p) :
    Continuous (Matrix.reindexAlgEquiv K K e) :=
  (Matrix.reindexAlgEquiv K K e).toLinearMap.continuous_of_finiteDimensional

/-- The construction `C` with its target reindexed along `e : m ≃ p`. -/
public def reindex {p : Type*} [Fintype p] [DecidableEq p] (C : TensorConstruction ℓ K n m)
    (e : m ≃ p) : TensorConstruction ℓ K n p where
  R := (Units.map (Matrix.reindexAlgEquiv K K e).toRingEquiv.toMonoidHom).comp C.R
  D := (Matrix.reindexLieEquiv (R := K) e).toLieHom.comp C.D
  norm_lt X hX := (norm_reindex_le e _).trans_lt (C.norm_lt X hX)
  map_eq g hg := by
    change Matrix.reindexAlgEquiv K K e (C.R g : Matrix m m K) =
      exp (Matrix.reindexAlgEquiv K K e (C.D (ladicLog ℓ (g : Matrix n n K))))
    rw [C.map_eq g hg]
    have hL : ‖ladicLog ℓ (g : Matrix n n K)‖ < (ℓ : ℝ)⁻¹ :=
      (norm_ladicLog_le hg.le).trans_lt hg
    exact map_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (Matrix.reindexAlgEquiv K K e).toRingEquiv.toRingHom
      (continuous_reindexAlgEquiv e) _ (mem_eball_expSeries (C.norm_lt _ hL))

omit [CharZero K] in
/-- The representation of `C.reindex e` is that of `C` with its matrices reindexed along `e`. -/
public theorem reindex_R_apply {p : Type*} [Fintype p] [DecidableEq p]
    (C : TensorConstruction ℓ K n m) (e : m ≃ p) (g : (Matrix n n K)ˣ) :
    ((C.reindex e).R g : Matrix p p K) = Matrix.reindex e e (C.R g : Matrix m m K) :=
  rfl

/-- **The `j`-th Kronecker power** `V ↦ C(V)^{⊗ j}` of a construction with target `Fin s`,
flattened to `Fin (s ^ j)` as `Stacks.EtaleCohomology.tensorPowerRepresentation` is. -/
public def kronPow {s : ℕ} (C : TensorConstruction ℓ K n (Fin s)) :
    (j : ℕ) → TensorConstruction ℓ K n (Fin (s ^ j))
  | 0 => unit
  | j + 1 => ((kronPow C j).kron C).reindex finProdFinEquiv

omit [CharZero K] in
/-- The zeroth Kronecker power of `C` is the trivial representation. -/
public theorem kronPow_R_zero {s : ℕ} (C : TensorConstruction ℓ K n (Fin s))
    (g : (Matrix n n K)ˣ) : ((kronPow C 0).R g : Matrix (Fin (s ^ 0)) (Fin (s ^ 0)) K) = 1 :=
  rfl

omit [CharZero K] in
/-- The `(j + 1)`-st Kronecker power of `C` is the Kronecker product of the `j`-th power with
`C`, flattened along `finProdFinEquiv`. -/
public theorem kronPow_R_succ {s : ℕ} (C : TensorConstruction ℓ K n (Fin s)) (j : ℕ)
    (g : (Matrix n n K)ˣ) :
    ((kronPow C (j + 1)).R g : Matrix (Fin (s ^ (j + 1))) (Fin (s ^ (j + 1))) K) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (((kronPow C j).R g : Matrix (Fin (s ^ j)) (Fin (s ^ j)) K) ⊗ₖ
          (C.R g : Matrix (Fin s) (Fin s) K)) :=
  rfl

end TensorConstruction

end Stacks.LAdic

end
