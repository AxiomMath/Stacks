module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel

/-!
# Integral block upper-triangular conjugates

Let `J : R^a → R^r` and `K : R^r → R^c` be a split short exact sequence of free modules given by
matrices with `J' J = 1`, `K K' = 1`, `K J = 0` and `J J' + K' K = 1` (for instance the inclusion
of and projection to complementary sets of coordinates). A matrix `T` with `T J = J α` and
`K T = γ K` is block upper triangular with diagonal blocks `α`, `γ`:
`T = J α J' + J β K + K' γ K` with `β = J' T K'`.

A continuous representation `T : G → GL_r(ℚ_ℓ)` of a compact group with such diagonal blocks
`α`, `γ` has an integral conjugate `P⁻¹ T P` which still has the integral models of `α` and `γ` as
diagonal blocks, so that the lattice it defines is compatible with the sub and the quotient:
`P = (J Pα J' + K' Pγ K) (J J' + ℓ ^ m K' K)` for `m` large.

## Main definitions

* `Stacks.EtaleCohomology.IsSplitting`: the relations `J' J = 1`, `K K' = 1`, `K J = 0`,
  `J' K' = 0` and `J J' + K' K = 1`.
* `Stacks.EtaleCohomology.IsSplitting.blockDiag`: the block diagonal matrix `J P J' + K' Q K`.
* `Stacks.EtaleCohomology.coordMatrix`: the matrix of a map of coordinates `Fin a → Fin r`.

## Main results

* `Stacks.EtaleCohomology.IsSplitting.exact`: `J` and `K` form an exact sequence
  `R^a → R^r → R^c`, with `J` injective (`Stacks.EtaleCohomology.IsSplitting.mulVec_injective`)
  and `K` surjective (`Stacks.EtaleCohomology.IsSplitting.mulVec_surjective`).
* `Stacks.EtaleCohomology.IsSplitting.eq_blocks`: the block decomposition of a matrix with
  `T J = J α` and `K T = γ K`.
* `Stacks.EtaleCohomology.isSplitting_coordMatrix`: complementary coordinate maps form a
  splitting.
* `Stacks.EtaleCohomology.IsSplitting.exists_integral_conj`: an integral conjugate with integral
  diagonal blocks.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Splitting

variable {R : Type*} [CommRing R] {r a c : ℕ} {J : Matrix (Fin r) (Fin a) R}
  {J' : Matrix (Fin a) (Fin r) R} {K : Matrix (Fin c) (Fin r) R} {K' : Matrix (Fin r) (Fin c) R}

/-- The splitting relations of a split short exact sequence `0 → R^a → R^r → R^c → 0`. -/
public structure IsSplitting (J : Matrix (Fin r) (Fin a) R) (J' : Matrix (Fin a) (Fin r) R)
    (K : Matrix (Fin c) (Fin r) R) (K' : Matrix (Fin r) (Fin c) R) : Prop where
  left_inv : J' * J = 1
  right_inv : K * K' = 1
  comp_zero : K * J = 0
  dual_comp_zero : J' * K' = 0
  sum_eq_one : J * J' + K' * K = 1

variable (h : IsSplitting J J' K K')
include h

/-- The first map of a splitting is injective. -/
public theorem IsSplitting.mulVec_injective : Function.Injective (J *ᵥ ·) := fun v w hvw => by
  simpa [Matrix.mulVec_mulVec, h.left_inv] using congrArg (J' *ᵥ ·) hvw

/-- The second map of a splitting is surjective. -/
public theorem IsSplitting.mulVec_surjective : Function.Surjective (K *ᵥ ·) := fun w =>
  ⟨K' *ᵥ w, by simp [Matrix.mulVec_mulVec, h.right_inv]⟩

/-- The two maps of a splitting form an exact sequence. -/
public theorem IsSplitting.exact : Function.Exact (J *ᵥ ·) (K *ᵥ ·) := fun w => by
  constructor
  · intro hw
    refine ⟨J' *ᵥ w, ?_⟩
    have h1 : (J * J' + K' * K) *ᵥ w = w := by rw [h.sum_eq_one, Matrix.one_mulVec]
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h1
    change K *ᵥ w = 0 at hw
    rwa [hw, Matrix.mulVec_zero, add_zero] at h1
  · rintro ⟨v, rfl⟩
    change K *ᵥ (J *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, h.comp_zero, Matrix.zero_mulVec]

/-- Ring homomorphisms preserve splittings. -/
public theorem IsSplitting.map {S : Type*} [CommRing S] (φ : R →+* S) :
    IsSplitting (J.map φ) (J'.map φ) (K.map φ) (K'.map φ) where
  left_inv := by rw [← Matrix.map_mul, h.left_inv, Matrix.map_one _ φ.map_zero φ.map_one]
  right_inv := by rw [← Matrix.map_mul, h.right_inv, Matrix.map_one _ φ.map_zero φ.map_one]
  comp_zero := by rw [← Matrix.map_mul, h.comp_zero, Matrix.map_zero _ φ.map_zero]
  dual_comp_zero := by rw [← Matrix.map_mul, h.dual_comp_zero, Matrix.map_zero _ φ.map_zero]
  sum_eq_one := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add φ), h.sum_eq_one,
      Matrix.map_one _ φ.map_zero φ.map_one]

/-- `J' (J X) = X`. -/
public theorem IsSplitting.left_inv' {n : Type*} (X : Matrix (Fin a) n R) :
    J' * (J * X) = X := by rw [← Matrix.mul_assoc, h.left_inv, Matrix.one_mul]

/-- `K (K' X) = X`. -/
public theorem IsSplitting.right_inv' {n : Type*} (X : Matrix (Fin c) n R) :
    K * (K' * X) = X := by rw [← Matrix.mul_assoc, h.right_inv, Matrix.one_mul]

/-- `K (J X) = 0`. -/
public theorem IsSplitting.comp_zero' {n : Type*} (X : Matrix (Fin a) n R) :
    K * (J * X) = 0 := by rw [← Matrix.mul_assoc, h.comp_zero, Matrix.zero_mul]

/-- `J' (K' X) = 0`. -/
public theorem IsSplitting.dual_comp_zero' {n : Type*} (X : Matrix (Fin c) n R) :
    J' * (K' * X) = 0 := by rw [← Matrix.mul_assoc, h.dual_comp_zero, Matrix.zero_mul]

/-- The block diagonal matrix `J P J' + K' Q K`. -/
public def IsSplitting.blockDiag (_h : IsSplitting J J' K K') (P : Matrix (Fin a) (Fin a) R)
    (Q : Matrix (Fin c) (Fin c) R) : Matrix (Fin r) (Fin r) R :=
  J * P * J' + K' * Q * K

/-- Block diagonal matrices multiply blockwise. -/
public theorem IsSplitting.blockDiag_mul (P P' : Matrix (Fin a) (Fin a) R)
    (Q Q' : Matrix (Fin c) (Fin c) R) :
    h.blockDiag P Q * h.blockDiag P' Q' = h.blockDiag (P * P') (Q * Q') := by
  simp only [IsSplitting.blockDiag, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    h.left_inv', h.right_inv', h.comp_zero', h.dual_comp_zero', Matrix.mul_zero, add_zero,
    zero_add]

/-- The block diagonal matrix with identity blocks is the identity. -/
public theorem IsSplitting.blockDiag_one : h.blockDiag 1 1 = 1 := by
  simp only [IsSplitting.blockDiag, Matrix.mul_one, h.sum_eq_one]

/-- `(J P J' + K' Q K) J = J P`. -/
public theorem IsSplitting.blockDiag_mul_J (P : Matrix (Fin a) (Fin a) R)
    (Q : Matrix (Fin c) (Fin c) R) : h.blockDiag P Q * J = J * P := by
  simp only [IsSplitting.blockDiag, Matrix.add_mul, Matrix.mul_assoc, h.left_inv, h.comp_zero,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

/-- `K (J P J' + K' Q K) = Q K`. -/
public theorem IsSplitting.K_mul_blockDiag (P : Matrix (Fin a) (Fin a) R)
    (Q : Matrix (Fin c) (Fin c) R) : K * h.blockDiag P Q = Q * K := by
  simp only [IsSplitting.blockDiag, Matrix.mul_add, ← Matrix.mul_assoc, h.right_inv, h.comp_zero,
    Matrix.one_mul, Matrix.zero_mul, zero_add]

/-- `(J P J' + K' Q K) K' = K' Q`. -/
public theorem IsSplitting.blockDiag_mul_K' (P : Matrix (Fin a) (Fin a) R)
    (Q : Matrix (Fin c) (Fin c) R) : h.blockDiag P Q * K' = K' * Q := by
  simp only [IsSplitting.blockDiag, Matrix.add_mul, Matrix.mul_assoc, h.right_inv,
    h.dual_comp_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]

/-- **Block decomposition.** If `T J = J α` and `K T = γ K`, then
`T = J α J' + J (J' T K') K + K' γ K`. -/
public theorem IsSplitting.eq_blocks {T : Matrix (Fin r) (Fin r) R} {α : Matrix (Fin a) (Fin a) R}
    {γ : Matrix (Fin c) (Fin c) R} (hJ : T * J = J * α) (hK : K * T = γ * K) :
    T = J * α * J' + J * (J' * T * K') * K + K' * γ * K := by
  have hJ' : ∀ {n : Type} [Fintype n] (X : Matrix (Fin a) n R), T * (J * X) = J * (α * X) :=
    fun X => by rw [← Matrix.mul_assoc, hJ, Matrix.mul_assoc]
  have hK' : ∀ {n : Type} [Fintype n] (X : Matrix (Fin r) n R), K * (T * X) = γ * (K * X) :=
    fun X => by rw [← Matrix.mul_assoc, hK, Matrix.mul_assoc]
  have e : T = (J * J' + K' * K) * T * (J * J' + K' * K) := by
    rw [h.sum_eq_one, Matrix.one_mul, Matrix.mul_one]
  conv_lhs => rw [e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJ', hK', h.left_inv',
    h.right_inv', h.comp_zero', Matrix.mul_zero, add_zero]
  abel

end Splitting

section Coordinates

variable {R : Type*} [CommRing R] {r a c : ℕ}

/-- The matrix of the coordinate map `R^a → R^r`, `e_j ↦ e_{e j}`. -/
public def coordMatrix (e : Fin a → Fin r) : Matrix (Fin r) (Fin a) R :=
  Matrix.of fun i j => if i = e j then 1 else 0

/-- A coordinate matrix is sent to the coordinate matrix by any ring homomorphism. -/
public theorem coordMatrix_map {S : Type*} [CommRing S] (φ : R →+* S) (e : Fin a → Fin r) :
    (coordMatrix (R := R) e).map φ = coordMatrix e := by
  ext i j
  simp only [coordMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- For injective `e`, `eᵀ e = 1`. -/
public theorem transpose_coordMatrix_mul_coordMatrix {e : Fin a → Fin r}
    (he : Function.Injective e) :
    (coordMatrix (R := R) e)ᵀ * coordMatrix (R := R) e = 1 := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · by_cases hj : j = j' <;> simp [coordMatrix, Matrix.one_apply, hj, he.eq_iff]
  · intro i _ hi
    simp [coordMatrix, hi]
  · simp

/-- For `e₁`, `e₂` with disjoint ranges, `e₂ᵀ e₁ = 0`. -/
public theorem transpose_coordMatrix_mul_coordMatrix_eq_zero {e₁ : Fin a → Fin r}
    {e₂ : Fin c → Fin r} (hdisj : ∀ j j', e₁ j ≠ e₂ j') :
    (coordMatrix (R := R) e₂)ᵀ * coordMatrix (R := R) e₁ = 0 := by
  ext j j'
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [coordMatrix, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h1 : i = e₂ j
  · subst h1
    simp [Ne.symm (hdisj j' j)]
  · simp [h1]

/-- For injective `e`, `e eᵀ` is the diagonal matrix of the indicator of the range of `e`. -/
public theorem coordMatrix_mul_transpose_apply {e : Fin a → Fin r} (he : Function.Injective e)
    (i i' : Fin r) :
    (coordMatrix (R := R) e * (coordMatrix (R := R) e)ᵀ) i i' =
      if i = i' ∧ ∃ j, e j = i then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [coordMatrix, he.eq_iff, Ne.symm hj'])
      (by simp)]
    by_cases h : e j = i'
    · subst h
      simp [coordMatrix]
    · have h' : i' ≠ e j := fun h' => h h'.symm
      simp [coordMatrix, h, h']
  · rw [Finset.sum_eq_zero fun j _ => by
      simp only [coordMatrix, Matrix.transpose_apply, Matrix.of_apply]
      rw [ite_eq_right fun h => hi ⟨j, h.symm⟩, zero_mul]]
    simp [hi]

/-- **A coordinate splitting**: for injective `e₁ : Fin a → Fin r`, `e₂ : Fin c → Fin r` with
disjoint ranges covering `Fin r`, the coordinate matrices form a splitting. -/
public theorem isSplitting_coordMatrix {e₁ : Fin a → Fin r} {e₂ : Fin c → Fin r}
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂) (hdisj : ∀ j j', e₁ j ≠ e₂ j')
    (hcov : ∀ i, (∃ j, e₁ j = i) ∨ (∃ j, e₂ j = i)) :
    IsSplitting (coordMatrix (R := R) e₁) (coordMatrix e₁)ᵀ (coordMatrix e₂)ᵀ
      (coordMatrix e₂) where
  left_inv := transpose_coordMatrix_mul_coordMatrix he₁
  right_inv := transpose_coordMatrix_mul_coordMatrix he₂
  comp_zero := transpose_coordMatrix_mul_coordMatrix_eq_zero hdisj
  dual_comp_zero := by
    have h := congrArg Matrix.transpose
      (transpose_coordMatrix_mul_coordMatrix_eq_zero (R := R) hdisj)
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  sum_eq_one := by
    ext i i'
    rw [Matrix.add_apply, coordMatrix_mul_transpose_apply he₁,
      coordMatrix_mul_transpose_apply he₂, Matrix.one_apply]
    rcases hcov i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have h2 : ¬ ∃ j', e₂ j' = e₁ j := fun ⟨j', hj'⟩ => hdisj j j' hj'.symm
      by_cases h : e₁ j = i'
      · subst h
        simp [h2]
      · simp [h]
    · have h1 : ¬ ∃ j', e₁ j' = e₂ j := fun ⟨j', hj'⟩ => hdisj j' j hj'
      by_cases h : e₂ j = i'
      · subst h
        simp [h1]
      · simp [h]

end Coordinates

section Lattice

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The norm of `ℓ ^ m x` decreases with `m`. -/
public theorem norm_pow_mul_le_of_le {m m' : ℕ} (hm : m ≤ m') (x : ℚ_[ℓ]) :
    ‖(ℓ : ℚ_[ℓ]) ^ m' * x‖ ≤ ‖(ℓ : ℚ_[ℓ]) ^ m * x‖ := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le
  have hc1 : ‖(ℓ : ℚ_[ℓ]) ^ c‖ ≤ 1 := by
    rw [Padic.norm_p_pow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hℓ)
  rw [pow_add, mul_comm ((ℓ : ℚ_[ℓ]) ^ m), mul_assoc, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc1

/-- **A continuous family of `ℚ_ℓ`-matrices on a compact space is uniformly integral after
multiplication by a power of `ℓ`.** -/
public theorem exists_pow_mul_norm_le_one_of_continuous {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {α β : Type*} [Finite α] [Finite β] (C : X → Matrix α β ℚ_[ℓ])
    (hC : Continuous C) : ∃ m : ℕ, ∀ x i j, ‖(ℓ : ℚ_[ℓ]) ^ m * C x i j‖ ≤ 1 := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hone : ∀ i j, ∃ m : ℕ, ∀ x, ‖(ℓ : ℚ_[ℓ]) ^ m * C x i j‖ ≤ 1 := fun i j => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      ((continuous_apply j).comp ((continuous_apply i).comp hC)).continuousOn
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B hℓ
    refine ⟨m, fun x => ?_⟩
    have hx := hB x (Set.mem_univ x)
    simp only [Function.comp_apply] at hx
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ m := pow_pos (by linarith) m
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hx.trans hm.le
  choose m hm using hone
  refine ⟨Finset.univ.sup fun ij : α × β => m ij.1 ij.2, fun x i j => ?_⟩
  exact (norm_pow_mul_le_of_le (Finset.le_sup (f := fun ij : α × β => m ij.1 ij.2)
    (Finset.mem_univ (i, j))) _).trans (hm i j x)

end Lattice

section Conj

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {r a c : ℕ} {J : Matrix (Fin r) (Fin a) ℤ_[ℓ]}
  {J' : Matrix (Fin a) (Fin r) ℤ_[ℓ]} {K : Matrix (Fin c) (Fin r) ℤ_[ℓ]}
  {K' : Matrix (Fin r) (Fin c) ℤ_[ℓ]}

/-- The unit `J P J' + K' Q K` of block diagonal matrices. -/
public def IsSplitting.blockDiagUnit {R : Type*} [CommRing R] {J : Matrix (Fin r) (Fin a) R}
    {J' : Matrix (Fin a) (Fin r) R} {K : Matrix (Fin c) (Fin r) R} {K' : Matrix (Fin r) (Fin c) R}
    (h : IsSplitting J J' K K') (P : GL (Fin a) R) (Q : GL (Fin c) R) : GL (Fin r) R :=
  ⟨h.blockDiag P.val Q.val, h.blockDiag P⁻¹.val Q⁻¹.val,
    by rw [h.blockDiag_mul, Units.mul_inv, Units.mul_inv, h.blockDiag_one],
    by rw [h.blockDiag_mul, Units.inv_mul, Units.inv_mul, h.blockDiag_one]⟩

/-- Conjugating by a block diagonal unit conjugates the diagonal blocks. -/
public theorem IsSplitting.conj_blockDiagUnit {R : Type*} [CommRing R]
    {J : Matrix (Fin r) (Fin a) R} {J' : Matrix (Fin a) (Fin r) R} {K : Matrix (Fin c) (Fin r) R}
    {K' : Matrix (Fin r) (Fin c) R} (h : IsSplitting J J' K K') (P : GL (Fin a) R)
    (Q : GL (Fin c) R) {T : Matrix (Fin r) (Fin r) R} {α : Matrix (Fin a) (Fin a) R}
    {γ : Matrix (Fin c) (Fin c) R} (hJ : T * J = J * α) (hK : K * T = γ * K) :
    (h.blockDiagUnit P Q)⁻¹.val * T * (h.blockDiagUnit P Q).val * J = J * (P⁻¹.val * α * P.val) ∧
      K * ((h.blockDiagUnit P Q)⁻¹.val * T * (h.blockDiagUnit P Q).val) =
        (Q⁻¹.val * γ * Q.val) * K := by
  have e1 : (h.blockDiagUnit P Q).val = h.blockDiag P.val Q.val := rfl
  have e2 : (h.blockDiagUnit P Q)⁻¹.val = h.blockDiag P⁻¹.val Q⁻¹.val := rfl
  rw [e1, e2]
  constructor
  · rw [Matrix.mul_assoc, h.blockDiag_mul_J, ← Matrix.mul_assoc, Matrix.mul_assoc _ T J, hJ,
      ← Matrix.mul_assoc, h.blockDiag_mul_J]
    simp only [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.K_mul_blockDiag, Matrix.mul_assoc _ K T, hK,
      Matrix.mul_assoc, Matrix.mul_assoc, h.K_mul_blockDiag]
    simp only [Matrix.mul_assoc]

/-- The `ℚ_ℓ`-points of the integral model of `ρ` are the conjugates of `ρ` by the chosen matrix. -/
private theorem val_map_integralModel {n : ℕ} (ρ : G →* GL (Fin n) ℚ_[ℓ]) (hρ : Continuous ρ)
    (g : G) : (integralModel ρ hρ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) =
      (exists_conj_integral ρ hρ).choose⁻¹.val * (ρ g).val *
        (exists_conj_integral ρ hρ).choose.val := by
  have h1 := congrArg Units.val (map_integralModel ρ hρ g)
  rwa [Units.val_mul, Units.val_mul] at h1

/-- **An integral conjugate with integral diagonal blocks.** Let `T : G → GL_r(ℚ_ℓ)` be a
continuous representation of a compact group which is block upper triangular for the splitting
`J, K` with diagonal blocks `α`, `γ`. Then there is `P ∈ GL_r(ℚ_ℓ)` and a continuous
`T₁ : G → GL_r(ℤ_ℓ)` lifting `P⁻¹ T P` which is block upper triangular for the integral
splitting with diagonal blocks the integral models of `α` and `γ`. -/
public theorem IsSplitting.exists_integral_conj (h : IsSplitting J J' K K')
    (T : G →* GL (Fin r) ℚ_[ℓ]) (hT : Continuous T)
    (α : G →* GL (Fin a) ℚ_[ℓ]) (hα : Continuous α) (γ : G →* GL (Fin c) ℚ_[ℓ])
    (hγ : Continuous γ)
    (hJ : ∀ g, (T g).val * J.map (PadicInt.Coe.ringHom (p := ℓ)) =
      J.map (PadicInt.Coe.ringHom (p := ℓ)) * (α g).val)
    (hK : ∀ g, K.map (PadicInt.Coe.ringHom (p := ℓ)) * (T g).val =
      (γ g).val * K.map (PadicInt.Coe.ringHom (p := ℓ))) :
    ∃ (P : GL (Fin r) ℚ_[ℓ]) (T₁ : G →* GL (Fin r) ℤ_[ℓ]), Continuous T₁ ∧
      (∀ g, (T₁ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) = (P⁻¹ * T g * P).val) ∧
      (∀ g, (T₁ g).val * J = J * (integralModel α hα g).val) ∧
      (∀ g, K * (T₁ g).val = (integralModel γ hγ g).val * K) := by
  classical
  set φ := PadicInt.Coe.ringHom (p := ℓ)
  have hq := h.map φ
  set Pα := (exists_conj_integral α hα).choose
  set Pγ := (exists_conj_integral γ hγ).choose
  have hℓ0 : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  let L : ℕ → GL (Fin c) ℚ_[ℓ] := fun m =>
    ⟨((ℓ : ℚ_[ℓ]) ^ m) • 1, ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        mul_inv_cancel₀ (pow_ne_zero _ hℓ0), one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        inv_mul_cancel₀ (pow_ne_zero _ hℓ0), one_smul]⟩
  set Q₀ := hq.blockDiagUnit Pα Pγ
  set T₀ : G → Matrix (Fin r) (Fin r) ℚ_[ℓ] := fun g => Q₀⁻¹.val * (T g).val * Q₀.val
  set β : G → Matrix (Fin a) (Fin c) ℚ_[ℓ] := fun g => J'.map φ * T₀ g * K'.map φ
  have hβc : Continuous β := by
    have hTc : Continuous fun g => (T g).val := Units.continuous_val.comp hT
    exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hTc).matrix_mul
      continuous_const)).matrix_mul continuous_const
  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le_one_of_continuous (ℓ := ℓ) β hβc
  set Z := hq.blockDiagUnit Pα (Pγ * L m)
  set Tm : G → Matrix (Fin r) (Fin r) ℚ_[ℓ] := fun g => Z⁻¹.val * (T g).val * Z.val
  have hblk := fun g => hq.conj_blockDiagUnit Pα (Pγ * L m) (hJ g) (hK g)
  have hLγ : ∀ g, (Pγ * L m)⁻¹.val * (γ g).val * (Pγ * L m).val = Pγ⁻¹.val * (γ g).val * Pγ.val :=
    fun g => by
      simp only [_root_.mul_inv_rev, Units.val_mul, L, Units.inv_mk]
      simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul, mul_inv_cancel₀ (pow_ne_zero m hℓ0), one_smul]
  have hTmJ : ∀ g, Tm g * J.map φ = J.map φ * (integralModel α hα g).val.map φ := fun g => by
    rw [val_map_integralModel]; exact (hblk g).1
  have hKTm : ∀ g, K.map φ * Tm g = (integralModel γ hγ g).val.map φ * K.map φ := fun g => by
    rw [val_map_integralModel, ← hLγ]; exact (hblk g).2
  have hZ : Z.val = Q₀.val * hq.blockDiag 1 (L m).val := by
    change hq.blockDiag Pα.val (Pγ * L m).val =
      hq.blockDiag Pα.val Pγ.val * hq.blockDiag 1 (L m).val
    rw [hq.blockDiag_mul, Matrix.mul_one, Units.val_mul]
  have hZi : Z⁻¹.val = hq.blockDiag 1 (L m)⁻¹.val * Q₀⁻¹.val := by
    change hq.blockDiag Pα⁻¹.val (Pγ * L m)⁻¹.val =
      hq.blockDiag 1 (L m)⁻¹.val * hq.blockDiag Pα⁻¹.val Pγ⁻¹.val
    rw [hq.blockDiag_mul, Matrix.one_mul, _root_.mul_inv_rev, Units.val_mul]
  have hJ'D : J'.map φ * hq.blockDiag 1 (L m)⁻¹.val = J'.map φ := by
    simp only [IsSplitting.blockDiag, Matrix.mul_add, ← Matrix.mul_assoc, hq.left_inv,
      hq.dual_comp_zero, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, add_zero]
  have hDK' : hq.blockDiag 1 (L m).val * K'.map φ = ((ℓ : ℚ_[ℓ]) ^ m) • K'.map φ := by
    simp only [IsSplitting.blockDiag, Matrix.add_mul, Matrix.mul_assoc, hq.right_inv,
      hq.dual_comp_zero, Matrix.mul_one, Matrix.mul_zero, zero_add, L]
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hoff : ∀ g, J'.map φ * Tm g * K'.map φ = ((ℓ : ℚ_[ℓ]) ^ m) • β g := fun g => by
    simp only [Tm, β, T₀, hZ, hZi]
    simp only [Matrix.mul_assoc]
    rw [hDK', ← Matrix.mul_assoc (J'.map φ) (hq.blockDiag 1 (L m)⁻¹.val), hJ'D]
    simp only [Matrix.mul_smul]
  let B : G → Matrix (Fin a) (Fin c) ℤ_[ℓ] := fun g => Matrix.of fun i j => ⟨_, hm g i j⟩
  have hB : ∀ g, (B g).map φ = ((ℓ : ℚ_[ℓ]) ^ m) • β g := fun g => by
    ext i j
    rfl
  have hTm : ∀ g, Tm g = (J * (integralModel α hα g).val * J' + J * B g * K +
      K' * (integralModel γ hγ g).val * K).map φ := fun g => by
    rw [hq.eq_blocks (hTmJ g) (hKTm g), hoff g, ← hB g, Matrix.map_add _ (map_add φ),
      Matrix.map_add _ (map_add φ)]
    simp only [Matrix.map_mul]
  have hint : ∀ g, IsIntegralMatrix (conjRepr T Z g).val := fun g i j => by
    rw [conjRepr_apply, Units.val_mul, Units.val_mul]
    change ‖Tm g i j‖ ≤ 1
    rw [hTm g, Matrix.map_apply]
    exact PadicInt.norm_le_one _
  have hc : Continuous (conjRepr T Z) := by
    have : (conjRepr T Z : G → GL (Fin r) ℚ_[ℓ]) = fun g => Z⁻¹ * T g * Z :=
      funext (conjRepr_apply T Z)
    rw [this]
    exact (continuous_const.mul hT).mul continuous_const
  have hlift : ∀ g, (integralLift (conjRepr T Z) hint g).val.map φ = Tm g := fun g => by
    have := mapMatrix_integralLift (conjRepr T Z) hint g
    rwa [conjRepr_apply, Units.val_mul, Units.val_mul] at this
  refine ⟨Z, integralLift (conjRepr T Z) hint, continuous_integralLift hint hc, fun g => ?_,
    fun g => ?_, fun g => ?_⟩
  · exact hlift g
  · apply Matrix.map_injective (f := φ) (fun a b h => PadicInt.ext h)
    dsimp only
    simp only [Matrix.map_mul]
    change (integralLift (conjRepr T Z) hint g).val.map φ * J.map φ = _
    rw [hlift]
    exact hTmJ g
  · apply Matrix.map_injective (f := φ) (fun a b h => PadicInt.ext h)
    dsimp only
    simp only [Matrix.map_mul]
    change K.map φ * (integralLift (conjRepr T Z) hint g).val.map φ = _
    rw [hlift]
    exact hKTm g

end Conj

end Stacks.EtaleCohomology

end
