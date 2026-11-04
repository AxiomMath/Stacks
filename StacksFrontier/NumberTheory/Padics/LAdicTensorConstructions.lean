module

public import StacksFrontier.NumberTheory.Padics.LAdicConstructions
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Tensor constructions of `ℓ`-adic representations

The constructions `(R, D)` of `Stacks.LAdic.det_stabRestrict_construction` closed under
composition, Kronecker products and duals: `Stacks.LAdic.TensorConstruction`.  Every
`V^{⊗a} ⊗ (V^∨)^{⊗b}` is obtained from the identity by these operations.

## Main definitions

* `Stacks.LAdic.TensorConstruction`: A group homomorphism `GL_n → GL_m` together with a Lie
  algebra homomorphism `D` with `R g = exp (D (log g))` near the identity.
* `Stacks.LAdic.TensorConstruction.id`, `Stacks.LAdic.TensorConstruction.comp`,
  `Stacks.LAdic.TensorConstruction.kron`, `Stacks.LAdic.TensorConstruction.dual`: The identity,
  composite, Kronecker product and dual constructions.

## Main results

* `Stacks.LAdic.exists_eq_mul_of_hasEigenvalue_kronecker`: Every eigenvalue of `A ⊗ₖ B` is a
  product of an eigenvalue of `A` and an eigenvalue of `B`.
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

variable (ℓ K) in
/-- A *tensor construction* from `GL_n` to `GL_m`: a group homomorphism `R` and a Lie algebra
homomorphism `D` with `R g = exp (D (log g))` on the disc `‖g - 1‖ < ℓ⁻¹`, and `D` mapping the
disc `‖X‖ < ℓ⁻¹` into itself. -/
structure TensorConstruction (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] where
  /-- The group homomorphism. -/
  R : (Matrix n n K)ˣ →* (Matrix m m K)ˣ
  /-- Its derivative. -/
  D : Matrix n n K →ₗ⁅K⁆ Matrix m m K
  norm_lt : ∀ X : Matrix n n K, ‖X‖ < (ℓ : ℝ)⁻¹ → ‖D X‖ < (ℓ : ℝ)⁻¹
  map_eq : ∀ g : (Matrix n n K)ˣ, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ →
    (R g : Matrix m m K) = exp (D (ladicLog ℓ (g : Matrix n n K)))

variable {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

namespace TensorConstruction

/-- The identity construction. -/
def id : TensorConstruction ℓ K n n where
  R := MonoidHom.id _
  D := LieHom.id
  norm_lt _ h := h
  map_eq _g hg := (exp_ladicLog hg).symm

/-- The composite of two constructions. -/
def comp (C₂ : TensorConstruction ℓ K m p) (C₁ : TensorConstruction ℓ K n m) :
    TensorConstruction ℓ K n p where
  R := C₂.R.comp C₁.R
  D := C₂.D.comp C₁.D
  norm_lt X h := C₂.norm_lt _ (C₁.norm_lt X h)
  map_eq g hg := by
    change (C₂.R (C₁.R g) : Matrix p p K) = _
    rw [C₂.map_eq _ (norm_map_sub_one_lt C₁.R C₁.D C₁.norm_lt C₁.map_eq hg),
      (congrArg (ladicLog ℓ) (C₁.map_eq g hg)).trans
        (ladicLog_exp (C₁.norm_lt _ ((norm_ladicLog_le hg.le).trans_lt hg)))]
    rfl

end TensorConstruction

omit [Fact ℓ.Prime] [CharZero K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- The norm of `a ⊗ₖ 1` is at most the norm of `a`. -/
theorem norm_kronecker_one_le (a : Matrix m m K) : ‖a ⊗ₖ (1 : Matrix p p K)‖ ≤ ‖a‖ := by
  rw [norm_le_iff (norm_nonneg _)]
  rintro ⟨i, j⟩ ⟨k, l⟩
  rw [kronecker_apply, norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (norm_entry_le_entrywise_sup_norm a)
  by_cases h : j = l
  · subst h
    simp
  · simp [h]

omit [Fact ℓ.Prime] [CharZero K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- The norm of `1 ⊗ₖ c` is at most the norm of `c`. -/
theorem norm_one_kronecker_le (c : Matrix p p K) : ‖(1 : Matrix m m K) ⊗ₖ c‖ ≤ ‖c‖ := by
  rw [norm_le_iff (norm_nonneg _)]
  rintro ⟨i, j⟩ ⟨k, l⟩
  rw [kronecker_apply, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_entry_le_entrywise_sup_norm c)
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- `X ↦ X ⊗ₖ 1` as a ring homomorphism. -/
def kronOneRingHom : Matrix m m K →+* Matrix (m × p) (m × p) K where
  toFun X := X ⊗ₖ (1 : Matrix p p K)
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := zero_kronecker _
  map_add' X Y := add_kronecker _ _ _

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- `Y ↦ 1 ⊗ₖ Y` as a ring homomorphism. -/
def oneKronRingHom : Matrix p p K →+* Matrix (m × p) (m × p) K where
  toFun Y := (1 : Matrix m m K) ⊗ₖ Y
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := kronecker_zero _
  map_add' X Y := kronecker_add _ _ _

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] in
/-- The map `X ↦ X ⊗ₖ 1` is continuous. -/
theorem continuous_kronOneRingHom :
    Continuous (kronOneRingHom (K := K) (m := m) (p := p)) := by
  let L : Matrix m m K →ₗ[K] Matrix (m × p) (m × p) K :=
    { toFun := fun X => X ⊗ₖ (1 : Matrix p p K)
      map_add' := fun X Y => add_kronecker _ _ _
      map_smul' := fun c X => smul_kronecker _ _ _ }
  exact L.continuous_of_finiteDimensional

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] in
/-- The map `Y ↦ 1 ⊗ₖ Y` is continuous. -/
theorem continuous_oneKronRingHom :
    Continuous (oneKronRingHom (K := K) (m := m) (p := p)) := by
  let L : Matrix p p K →ₗ[K] Matrix (m × p) (m × p) K :=
    { toFun := fun Y => (1 : Matrix m m K) ⊗ₖ Y
      map_add' := fun X Y => kronecker_add _ _ _
      map_smul' := fun c X => kronecker_smul _ _ _ }
  exact L.continuous_of_finiteDimensional

namespace TensorConstruction

/-- The Kronecker product of two constructions: `V ↦ C₁ V ⊗ C₂ V`. -/
def kron (C₁ : TensorConstruction ℓ K n m) (C₂ : TensorConstruction ℓ K n p) :
    TensorConstruction ℓ K n (m × p) where
  R :=
    { toFun := fun g =>
        ⟨(C₁.R g : Matrix m m K) ⊗ₖ (C₂.R g : Matrix p p K),
          (C₁.R g⁻¹ : Matrix m m K) ⊗ₖ (C₂.R g⁻¹ : Matrix p p K),
          by rw [← mul_kronecker_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
              mul_inv_cancel, map_one, map_one, Units.val_one, Units.val_one, one_kronecker_one],
          by rw [← mul_kronecker_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
              inv_mul_cancel, map_one, map_one, Units.val_one, Units.val_one, one_kronecker_one]⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [mul_kronecker_mul] }
  D :=
    { toFun := fun X => kronOneRingHom (p := p) (C₁.D X) + oneKronRingHom (m := m) (C₂.D X)
      map_add' := fun X Y => by
        simp only [map_add]
        abel
      map_smul' := fun c X => by
        simp only [map_smul, RingHom.id_apply, smul_add]
        simp only [kronOneRingHom, oneKronRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, smul_kronecker, kronecker_smul]
      map_lie' := fun {X Y} => by
        have hfg : ∀ (x : Matrix m m K) (y : Matrix p p K),
            kronOneRingHom (p := p) x * oneKronRingHom (m := m) y =
              oneKronRingHom (m := m) y * kronOneRingHom (p := p) x := fun x y => by
          simp only [kronOneRingHom, oneKronRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, ← mul_kronecker_mul, mul_one, one_mul]
        simp only [LieHom.map_lie]
        simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, mul_add, add_mul, hfg]
        abel }
  norm_lt X hX := by
    change ‖C₁.D X ⊗ₖ (1 : Matrix p p K) + (1 : Matrix m m K) ⊗ₖ C₂.D X‖ < _
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt
      ((norm_kronecker_one_le _).trans_lt (C₁.norm_lt X hX))
      ((norm_one_kronecker_le _).trans_lt (C₂.norm_lt X hX)))
  map_eq g hg := by
    change (C₁.R g : Matrix m m K) ⊗ₖ (C₂.R g : Matrix p p K) =
      exp (C₁.D (ladicLog ℓ (g : Matrix n n K)) ⊗ₖ (1 : Matrix p p K) +
        (1 : Matrix m m K) ⊗ₖ C₂.D (ladicLog ℓ (g : Matrix n n K)))
    set L := ladicLog ℓ (g : Matrix n n K)
    have hL : ‖L‖ < (ℓ : ℝ)⁻¹ := (norm_ladicLog_le hg.le).trans_lt hg
    have h1 := C₁.norm_lt L hL
    have h2 := C₂.norm_lt L hL
    have hcomm : Commute (C₁.D L ⊗ₖ (1 : Matrix p p K)) ((1 : Matrix m m K) ⊗ₖ C₂.D L) := by
      rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul,
        mul_one, one_mul]
    have e1 : exp (C₁.D L ⊗ₖ (1 : Matrix p p K)) = exp (C₁.D L) ⊗ₖ (1 : Matrix p p K) :=
      (map_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (kronOneRingHom (p := p)) continuous_kronOneRingHom _
        (mem_eball_expSeries h1)).symm
    have e2 : exp ((1 : Matrix m m K) ⊗ₖ C₂.D L) = (1 : Matrix m m K) ⊗ₖ exp (C₂.D L) :=
      (map_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (oneKronRingHom (m := m)) continuous_oneKronRingHom _
        (mem_eball_expSeries h2)).symm
    have e3 := exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) hcomm
      (mem_eball_expSeries ((norm_kronecker_one_le _).trans_lt h1))
      (mem_eball_expSeries ((norm_one_kronecker_le _).trans_lt h2))
    rw [C₁.map_eq g hg, C₂.map_eq g hg]
    have e4 : exp (C₁.D L) ⊗ₖ exp (C₂.D L) =
        (exp (C₁.D L) ⊗ₖ (1 : Matrix p p K)) * ((1 : Matrix m m K) ⊗ₖ exp (C₂.D L)) := by
      rw [← mul_kronecker_mul, mul_one, one_mul]
    exact e4.trans ((congrArg₂ (· * ·) e1.symm e2.symm).trans e3.symm)

/-- The dual construction `V ↦ V^∨`: `g ↦ (g⁻¹)ᵀ`, `X ↦ -Xᵀ`. -/
def dual : TensorConstruction ℓ K n n where
  R :=
    { toFun := fun g => ⟨((g⁻¹ : (Matrix n n K)ˣ) : Matrix n n K)ᵀ, (g : Matrix n n K)ᵀ,
          by rw [← transpose_mul, Units.mul_inv, transpose_one],
          by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [_root_.mul_inv_rev, transpose_mul] }
  D :=
    { toFun := fun X => -Xᵀ
      map_add' := fun X Y => by
        simp only [transpose_add, neg_add]
      map_smul' := fun c X => by simp [transpose_smul]
      map_lie' := fun {X Y} => by
        simp only [LieRing.of_associative_ring_bracket, transpose_sub, transpose_mul, neg_mul,
          mul_neg, neg_neg, neg_sub] }
  norm_lt X hX := by
    change ‖-Xᵀ‖ < _
    rwa [norm_neg, norm_transpose]
  map_eq g hg := by
    change ((g⁻¹ : (Matrix n n K)ˣ) : Matrix n n K)ᵀ = exp (-(ladicLog ℓ (g : Matrix n n K))ᵀ)
    set L := ladicLog ℓ (g : Matrix n n K)
    have hL : ‖L‖ < (ℓ : ℝ)⁻¹ := (norm_ladicLog_le hg.le).trans_lt hg
    have hL' : ‖-L‖ < (ℓ : ℝ)⁻¹ := by rwa [norm_neg]
    have hinv : exp (-L) = ((g⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) := by
      have h := exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) (Commute.neg_left (Commute.refl L))
        (mem_eball_expSeries hL') (mem_eball_expSeries hL)
      rw [neg_add_cancel, exp_zero, exp_ladicLog hg] at h
      exact (Units.inv_eq_of_mul_eq_one_left h.symm).symm
    rw [← hinv, ← transpose_neg]
    exact (Matrix.exp_transpose (-L)).symm

end TensorConstruction

/-! ### Eigenvalues of Kronecker products -/

section KroneckerEigen

variable {F : Type*} [Field F] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

/-- The tensor product of two vectors, indexed by pairs. -/
def vecTensor (v : m → F) (w : p → F) : m × p → F := fun q => v q.1 * w q.2

omit [DecidableEq m] [DecidableEq p] in
/-- `(A ⊗ₖ B) (v ⊗ w) = A v ⊗ B w`. -/
theorem kronecker_mulVec_vecTensor (A : Matrix m m F) (B : Matrix p p F) (v : m → F)
    (w : p → F) : (A ⊗ₖ B) *ᵥ vecTensor v w = vecTensor (A *ᵥ v) (B *ᵥ w) := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, vecTensor, kronecker_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] in
/-- `0 ⊗ w = 0`. -/
@[simp] theorem vecTensor_zero_left (w : p → F) : vecTensor (0 : m → F) w = 0 := by
  ext q
  simp [vecTensor]

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] in
/-- `v ⊗ 0 = 0`. -/
@[simp] theorem vecTensor_zero_right (v : m → F) : vecTensor v (0 : p → F) = 0 := by
  ext q
  simp [vecTensor]

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] in
/-- `(v₁ + v₂) ⊗ w = v₁ ⊗ w + v₂ ⊗ w`. -/
theorem vecTensor_add_left (v₁ v₂ : m → F) (w : p → F) :
    vecTensor (v₁ + v₂) w = vecTensor v₁ w + vecTensor v₂ w := by
  ext q
  simp [vecTensor, add_mul]

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] in
/-- `v ⊗ (w₁ + w₂) = v ⊗ w₁ + v ⊗ w₂`. -/
theorem vecTensor_add_right (v : m → F) (w₁ w₂ : p → F) :
    vecTensor v (w₁ + w₂) = vecTensor v w₁ + vecTensor v w₂ := by
  ext q
  simp [vecTensor, mul_add]

/-- `(A ⊗ₖ B) ^ k = A ^ k ⊗ₖ B ^ k`. -/
theorem kronecker_pow (A : Matrix m m F) (B : Matrix p p F) (k : ℕ) :
    (A ⊗ₖ B) ^ k = (A ^ k) ⊗ₖ (B ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- A vector `v` lies in the generalized `μ`-eigenspace of a matrix `M` if and only if
`(M - μ • 1) ^ k *ᵥ v = 0` for some `k`. -/
theorem mem_maxGenEigenspace_toLin'_iff {M : Matrix m m F} {μ : F} {v : m → F} :
    v ∈ (Module.End.maxGenEigenspace (Matrix.toLin' M)) μ ↔
      ∃ k : ℕ, ((M - μ • 1) ^ k) *ᵥ v = 0 := by
  rw [Module.End.mem_maxGenEigenspace]
  refine exists_congr fun k => ?_
  have : (Matrix.toLin' M - μ • (1 : Module.End F (m → F))) ^ k =
      Matrix.toLinAlgEquiv' ((M - μ • 1) ^ k) := by
    simp [map_pow, map_sub, map_smul, Matrix.toLinAlgEquiv'_one, Module.End.one_eq_id]
    rfl
  rw [this, Matrix.toLinAlgEquiv'_apply]

/-- If `M ^ a` kills `v`, then so does `M ^ k` for `a ≤ k`. -/
private theorem pow_mulVec_eq_zero_of_le {M : Matrix m m F} {v : m → F} {a k : ℕ}
    (h : (M ^ a) *ᵥ v = 0) (hak : a ≤ k) : (M ^ k) *ᵥ v = 0 := by
  rw [← Nat.sub_add_cancel hak, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- Tensor products of generalized eigenvectors are generalized eigenvectors. -/
theorem vecTensor_mem_maxGenEigenspace {A : Matrix m m F} {B : Matrix p p F} {μ ν : F}
    {v : m → F} {w : p → F} (hv : v ∈ (Module.End.maxGenEigenspace (Matrix.toLin' A)) μ)
    (hw : w ∈ (Module.End.maxGenEigenspace (Matrix.toLin' B)) ν) :
    vecTensor v w ∈ (Module.End.maxGenEigenspace (Matrix.toLin' (A ⊗ₖ B))) (μ * ν) := by
  rw [mem_maxGenEigenspace_toLin'_iff] at hv hw ⊢
  obtain ⟨a, ha⟩ := hv
  obtain ⟨b, hb⟩ := hw
  set X := (A - μ • 1) ⊗ₖ B
  set Y := μ • ((1 : Matrix m m F) ⊗ₖ (B - ν • 1))
  have hXY : A ⊗ₖ B - (μ * ν) • (1 : Matrix (m × p) (m × p) F) = X + Y := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [X, Y, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, kronecker_apply,
      Matrix.one_apply, smul_eq_mul, Prod.mk.injEq]
    split_ifs <;> simp_all <;> ring
  have hcomm : Commute X Y := by
    simp only [X, Y, Commute, SemiconjBy, mul_smul_comm, smul_mul_assoc, ← mul_kronecker_mul,
      mul_one, one_mul, mul_sub, sub_mul]
  refine ⟨a + b, ?_⟩
  rw [hXY, hcomm.add_pow, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hXk : X ^ k = ((A - μ • 1) ^ k) ⊗ₖ (B ^ k) := kronecker_pow _ _ _
  have hYj : ∀ j, Y ^ j = μ ^ j • ((1 : Matrix m m F) ⊗ₖ ((B - ν • 1) ^ j)) := fun j => by
    rw [smul_pow, kronecker_pow, one_pow]
  rw [← Nat.cast_comm, ← mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXk, hYj,
    Matrix.smul_mulVec, kronecker_mulVec_vecTensor, Matrix.one_mulVec, Matrix.mulVec_smul,
    kronecker_mulVec_vecTensor]
  rcases le_or_gt a k with hak | hak
  · simp [pow_mulVec_eq_zero_of_le ha hak]
  · simp [pow_mulVec_eq_zero_of_le hb (show b ≤ a + b - k by omega)]

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] in
/-- The standard basis vector at `q = (i, j)` is the tensor product of the standard basis vectors
at `i` and at `j`. -/
theorem single_eq_vecTensor [DecidableEq m] [DecidableEq p] (q : m × p) :
    (fun j => if q = j then (1 : F) else 0) = vecTensor (Pi.single q.1 1) (Pi.single q.2 1) := by
  ext ⟨i, j⟩
  obtain ⟨q1, q2⟩ := q
  simp only [vecTensor, Pi.single_apply, Prod.mk.injEq]
  by_cases h1 : i = q1 <;> by_cases h2 : j = q2 <;> simp [h1, h2, eq_comm]

/-- A subspace containing all tensor products of vectors is everything. -/
theorem mem_of_forall_vecTensor_mem {M : Submodule F (m × p → F)}
    (h : ∀ (v : m → F) (w : p → F), vecTensor v w ∈ M) (x : m × p → F) : x ∈ M := by
  rw [pi_eq_sum_univ x]
  refine M.sum_mem fun q _ => M.smul_mem _ ?_
  rw [single_eq_vecTensor]
  exact h _ _

omit [Fintype m] [DecidableEq m] in
/-- An eigenvector for `μ` lies in the generalized `μ`-eigenspace. -/
theorem mem_maxGenEigenspace_of_hasEigenvector {M : Type*} [AddCommGroup M] [Module F M]
    {f : Module.End F M} {μ : F} {x : M} (hx : f.HasEigenvector μ x) :
    x ∈ f.maxGenEigenspace μ :=
  (f.genEigenspace μ).monotone (show (1 : ℕ∞) ≤ ⊤ from le_top) hx.1

omit [Fintype m] [DecidableEq m] in
/-- An eigenvector lying in the sum of the generalized eigenspaces for a set `P` of scalars has
its eigenvalue in `P`. -/
theorem mem_of_hasEigenvector_mem_iSup {M : Type*} [AddCommGroup M] [Module F M]
    {f : Module.End F M} {P : F → Prop} {lam : F} {x : M} (hx : f.HasEigenvector lam x)
    (hxP : x ∈ ⨆ (κ : F) (_ : P κ), f.maxGenEigenspace κ) : P lam := by
  by_contra hne
  have hle : (⨆ (κ : F) (_ : P κ), f.maxGenEigenspace κ) ≤
      ⨆ (κ : F) (_ : κ ≠ lam), f.maxGenEigenspace κ := by
    refine iSup₂_le fun κ hκ => le_iSup₂_of_le κ ?_ le_rfl
    rintro rfl
    exact hne hκ
  exact hx.2 ((Submodule.disjoint_def.mp ((Module.End.independent_maxGenEigenspace f) lam)) x
    (mem_maxGenEigenspace_of_hasEigenvector hx) (hle hxP))

/-- The sum of the generalized eigenspaces of `A ⊗ₖ B` for products of eigenvalues. -/
def prodEigenPart (A : Matrix m m F) (B : Matrix p p F) : Submodule F (m × p → F) :=
  ⨆ (κ : F) (_ : ∃ μ ν, Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    Module.End.HasEigenvalue (Matrix.toLin' B) ν ∧ κ = μ * ν),
    Module.End.maxGenEigenspace (Matrix.toLin' (A ⊗ₖ B)) κ

omit [Fintype m] [DecidableEq m] in
/-- If a nonzero vector lies in the generalized `μ`-eigenspace of `f`, then `μ` is an eigenvalue
of `f`. -/
theorem hasEigenvalue_of_mem_maxGenEigenspace {f : Module.End F (m → F)} {μ : F} {v : m → F}
    (hv : v ∈ Module.End.maxGenEigenspace f μ) (hv0 : v ≠ 0) : Module.End.HasEigenvalue f μ :=
  Module.End.HasUnifEigenvalue.lt (k := ⊤) zero_lt_one fun hbot => hv0
    ((Submodule.mem_bot F).mp (by rwa [Module.End.maxGenEigenspace, hbot] at hv))

/-- The tensor product of generalized eigenvectors of `A` and of `B` lies in
`prodEigenPart A B`. -/
theorem vecTensor_mem_prodEigenPart_of_mem {A : Matrix m m F} {B : Matrix p p F} {μ ν : F}
    {v : m → F} {w : p → F} (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) μ)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' B) ν) :
    vecTensor v w ∈ prodEigenPart A B := by
  by_cases hv0 : v = 0
  · simp [hv0]
  by_cases hw0 : w = 0
  · simp [hw0]
  have hμ := hasEigenvalue_of_mem_maxGenEigenspace hv hv0
  have hν := hasEigenvalue_of_mem_maxGenEigenspace hw hw0
  exact (le_iSup₂_of_le (f := fun (κ : F) (_ : ∃ μ ν, Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    Module.End.HasEigenvalue (Matrix.toLin' B) ν ∧ κ = μ * ν) =>
      Module.End.maxGenEigenspace (Matrix.toLin' (A ⊗ₖ B)) κ) (μ * ν) ⟨μ, ν, hμ, hν, rfl⟩ le_rfl)
    (vecTensor_mem_maxGenEigenspace hv hw)

variable [IsAlgClosed F]

/-- Over an algebraically closed field, every vector lies in the sum of the generalized
eigenspaces of a matrix. -/
private theorem mem_iSup_maxGenEigenspace_toLin' (M : Matrix m m F) (v : m → F) :
    v ∈ ⨆ μ, Module.End.maxGenEigenspace (Matrix.toLin' M) μ := by
  rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial

/-- Over an algebraically closed field, `prodEigenPart A B` is the whole space. -/
theorem prodEigenPart_eq_top (A : Matrix m m F) (B : Matrix p p F) : prodEigenPart A B = ⊤ := by
  refine eq_top_iff.mpr fun x _ => mem_of_forall_vecTensor_mem (fun v w => ?_) x
  have hv := mem_iSup_maxGenEigenspace_toLin' A v
  have hw := mem_iSup_maxGenEigenspace_toLin' B w
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    induction hw using Submodule.iSup_induction' with
    | mem ν w hw => exact vecTensor_mem_prodEigenPart_of_mem hv hw
    | zero => rw [vecTensor_zero_right]; exact Submodule.zero_mem _
    | add w₁ w₂ _ _ h₁ h₂ => rw [vecTensor_add_right]; exact Submodule.add_mem _ h₁ h₂
  | zero => rw [vecTensor_zero_left]; exact Submodule.zero_mem _
  | add v₁ v₂ _ _ h₁ h₂ => rw [vecTensor_add_left]; exact Submodule.add_mem _ h₁ h₂

/-- **The eigenvalues of a Kronecker product are products of eigenvalues.** -/
theorem exists_eq_mul_of_hasEigenvalue_kronecker {A : Matrix m m F} {B : Matrix p p F} {lam : F}
    (h : Module.End.HasEigenvalue (Matrix.toLin' (A ⊗ₖ B)) lam) :
    ∃ μ ν, Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
      Module.End.HasEigenvalue (Matrix.toLin' B) ν ∧ lam = μ * ν := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hxM : x ∈ prodEigenPart A B := (prodEigenPart_eq_top A B).symm ▸ Submodule.mem_top
  exact mem_of_hasEigenvector_mem_iSup (F := F) (P := fun κ => ∃ μ ν,
    Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧ Module.End.HasEigenvalue (Matrix.toLin' B) ν ∧
      κ = μ * ν) hx hxM

end KroneckerEigen

end Stacks.LAdic
