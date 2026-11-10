module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerConstruction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.KroneckerPowerGraded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantEigenvector

/-!
# Frobenius on the geometric coinvariants of `(⋀ᵏ ρ)^{⊗ 2i}`

This is the bound on `H²_c` in Deligne's Lemme 1.5.2 of Weil II (Kedlaya, *Fourier transforms and
p-adic Weil II*, Lemma 6.5.1), for the tensor constructions `(⋀ᵏ ρ)^{⊗ 2i}`.

Let `ρ : Γ → GL_r(ℚ_ℓ)` be a representation, `H ⊴ Γ` (the geometric fundamental group) and
`φ ∈ Γ` (a geometric Frobenius).  Over a complete algebraically closed `K ⊇ ℚ_ℓ`, conjugate `ρ` by
`P₀` into graded upper triangular form along a flag of subrepresentations, with semisimplification
`σ'` (the graded diagonal part).  Let `u = σ'(φ^κ)` have the decomposition
`u ^ ℓ ^ N = exp A · exp B` of Weil II 1.3.9 relative to a finite index part `G` of `σ'(H)`, and
`z = exp B`.  Then every eigenvalue `μ` of `φ` on the `H`-coinvariants of `(⋀ᵏ ρ)^{⊗ 2i}` satisfies
`‖ι μ‖ ^ (κ ℓ ^ N) ≤ T ^ (2 i)` as soon as `T ≥ ‖ι c‖` for every root `c` of the characteristic
polynomial of `⋀ᵏ z`.

## Main definitions

* `Stacks.EtaleCohomology.extTensorHom`: the map `Y ↦ (⋀ᵏ Y)^{⊗ j}` on matrices.
* `Stacks.EtaleCohomology.extTensorGrading`: the grading of the coordinates of `(⋀ᵏ V)^{⊗ j}`
  induced by a grading of `V`.
* `Stacks.EtaleCohomology.dualExtTensorConstruction`: the dual of the construction
  `(⋀ᵏ)^{⊗ j}`.

## Main results

* `Stacks.EtaleCohomology.norm_le_pow_of_isRoot_charpoly_kronPowMatrix`: the roots of the
  characteristic polynomial of `A^{⊗ j}` are bounded by the `j`-th power of a bound for those of
  `A`.
* `Stacks.EtaleCohomology.norm_pow_le_of_isRoot_coinvariantsFrobenius`: the bound
  `‖ι μ‖ ^ (κ ℓ ^ N) ≤ T ^ i` on the Frobenius eigenvalues on the geometric coinvariants of
  `(⋀ᵏ ρ)^{⊗ i}`.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix Polynomial Stacks.LAdic
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K]

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- **The eigenvalues of a Kronecker power are products of eigenvalues**: if every root `c` of the
characteristic polynomial of `A` has `‖ι c‖ ≤ T`, every root of that of `A^{⊗ j}` has
`‖ι c‖ ≤ T ^ j`. -/
public theorem norm_le_pow_of_isRoot_charpoly_kronPowMatrix [IsAlgClosed K] (ι : K →+* ℂ) {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {T : ℝ} (hT : 0 ≤ T)
    (hA : ∀ c, A.charpoly.IsRoot c → ‖ι c‖ ≤ T) (j : ℕ) (c : K)
    (hc : (kronPowMatrix A j).charpoly.IsRoot c) : ‖ι c‖ ≤ T ^ j := by
  induction j generalizing c with
  | zero =>
    change (1 : Matrix (Fin (s ^ 0)) (Fin (s ^ 0)) K).charpoly.IsRoot c at hc
    rw [Matrix.charpoly_one, Fintype.card_fin, pow_zero, pow_one, IsRoot, eval_sub, eval_X,
      eval_one, sub_eq_zero] at hc
    rw [hc, map_one, norm_one, pow_zero]
  | succ j ih =>
    change (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (kronPowMatrix A j ⊗ₖ A)).charpoly.IsRoot c at hc
    rw [Matrix.charpoly_reindex, ← Matrix.charpoly_toLin',
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hc
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := exists_eq_mul_of_hasEigenvalue_kronecker hc
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin'] at hμ hν
    rw [map_mul, norm_mul, pow_succ]
    exact mul_le_mul (ih μ hμ) (hA ν hν) (norm_nonneg _) (pow_nonneg hT j)

section ExtTensor

variable {R : Type*} [CommRing R] {r : ℕ} (k j : ℕ)

/-- `Y ↦ (⋀ᵏ Y)^{⊗ j}` on matrices, in the coordinates of
`Stacks.EtaleCohomology.tensorPowerRepresentation` and
`Stacks.EtaleCohomology.exteriorPowerRepresentation`. -/
public def extTensorHom :
    Matrix (Fin r) (Fin r) R →* Matrix (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j))
      (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j)) R where
  toFun Y := kronPowMatrix (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
    (compoundMonoidHom k Y)) j
  map_one' := by
    simp only [map_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv, kronPowMatrix_one]
  map_mul' Y Y' := by
    simp only [map_mul, Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv _ _ _ (Fintype.equivFin _).symm, kronPowMatrix_mul]

/-- `extTensorHom` commutes with applying a ring homomorphism to the entries. -/
public theorem extTensorHom_map {S : Type*} [CommRing S] (f : R →+* S)
    (Y : Matrix (Fin r) (Fin r) R) :
    (extTensorHom k j Y).map f = extTensorHom k j (Y.map f) := by
  change (kronPowMatrix _ j).map f = kronPowMatrix _ j
  rw [kronPowMatrix_map, ← compoundMonoidHom_map]
  rfl

/-- The matrix of `(⋀ᵏ ρ)^{⊗ j}` at `g` is `extTensorHom k j (ρ g)`. -/
public theorem tensorPowerRepresentation_exteriorPowerRepresentation_val {Γ : Type*} [Group Γ]
    (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    (tensorPowerRepresentation (exteriorPowerRepresentation k ρ) j g : Matrix _ _ R) =
      extTensorHom k j (ρ g : Matrix (Fin r) (Fin r) R) := by
  rw [tensorPowerRepresentation_val, exteriorPowerRepresentation_val]
  rfl

/-- The grading of the coordinates of `(⋀ᵏ V)^{⊗ j}` induced by a grading of `V`. -/
public def extTensorGrading (d : Fin r → ℤ) :
    Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j) → ℤ :=
  kronPowGrading (subsetGrading k d ∘ (Fintype.equivFin _).symm) j

/-- `extTensorHom` carries graded upper triangular matrices to graded upper triangular matrices,
for the grading `extTensorGrading`. -/
public theorem IsGradedUpper.extTensorHom {d : Fin r → ℤ} {Y : Matrix (Fin r) (Fin r) R}
    (hY : IsGradedUpper d Y) : IsGradedUpper (extTensorGrading k j d) (extTensorHom k j Y) :=
  ((hY.compound k).reindex (Fintype.equivFin _)).kronPowMatrix j

/-- `extTensorHom` commutes with taking the graded diagonal part of a graded upper triangular
matrix. -/
public theorem gradedDiag_extTensorHom {d : Fin r → ℤ} {Y : Matrix (Fin r) (Fin r) R}
    (hY : IsGradedUpper d Y) :
    gradedDiag (extTensorGrading k j d) (extTensorHom k j Y) =
      extTensorHom k j (gradedDiag d Y) := by
  change gradedDiag (kronPowGrading (subsetGrading k d ∘ (Fintype.equivFin _).symm) j)
    (kronPowMatrix _ j) = kronPowMatrix _ j
  rw [gradedDiag_kronPowMatrix ((hY.compound k).reindex (Fintype.equivFin _)), gradedDiag_reindex,
    gradedDiag_compound k hY]

end ExtTensor

section Main

/-- If `w` is fixed by `M * N` and is a left eigenvector of `M` with eigenvalue `c`, then `c ≠ 0`
and `w` is a left eigenvector of `N` with eigenvalue `c⁻¹`. -/
private theorem vecMul_eq_inv_smul_of_vecMul_mul_eq {F m : Type*} [Field F] [Fintype m]
    {w : m → F} {M N : Matrix m m F} {c : F} (hw0 : w ≠ 0) (h : w ᵥ* (M * N) = w)
    (hM : w ᵥ* M = c • w) :
    c ≠ 0 ∧ w ᵥ* N = c⁻¹ • w := by
  rw [← Matrix.vecMul_vecMul, hM, Matrix.smul_vecMul] at h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact hw0 h.symm
  exact ⟨hc, by rw [eq_inv_smul_iff₀ hc]; exact h⟩

variable [IsAlgClosed K] {Γ : Type*} [Group Γ] {r : ℕ}

/-- The dual of the construction `(⋀ᵏ)^{⊗ j}`. -/
public def dualExtTensorConstruction (k j : ℕ) :
    TensorConstruction ℓ K (Fin r) (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j)) :=
  TensorConstruction.dual.comp ((exteriorConstruction k).kronPow j)

omit [IsAlgClosed K] in
/-- The matrix of `dualExtTensorConstruction k j` at `x` is the transpose of
`extTensorHom k j x⁻¹`. -/
public theorem dualExtTensorConstruction_R (k j : ℕ) (x : (Matrix (Fin r) (Fin r) K)ˣ) :
    ((dualExtTensorConstruction (ℓ := ℓ) k j).R x : Matrix _ _ K) =
      (extTensorHom k j ((x⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K))ᵀ := by
  change ((((((exteriorConstruction (ℓ := ℓ) k).kronPow j).R x)⁻¹ :
    (Matrix (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j))
      (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j)) K)ˣ) :
        Matrix (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j))
          (Fin (Fintype.card (Set.powersetCard (Fin r) k) ^ j)) K))ᵀ = _
  rw [← map_inv, kronPow_R_eq, exteriorConstruction_R]
  rfl

/-- **The Frobenius eigenvalues on the geometric coinvariants of `(⋀ᵏ ρ)^{⊗ i}` are bounded by the
determinantal weights** (Weil II 1.5.2, the `H²_c` term; Kedlaya, Lemma 6.5.1). -/
public theorem norm_pow_le_of_isRoot_coinvariantsFrobenius (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (ρ : Γ →* GL (Fin r) ℚ_[ℓ]) (P₀ : (Matrix (Fin r) (Fin r) K)ˣ)
    (d : Fin r → ℤ) (σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσ' : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d
      (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
          (P₀ : Matrix (Fin r) (Fin r) K)))
    (κ : ℕ) {G : Subgroup (Matrix (Fin r) (Fin r) K)ˣ} (hGH : ∀ g ∈ G, ∃ h ∈ H, σ' h = g)
    (hG : ∀ g ∈ G, ‖(g : Matrix (Fin r) (Fin r) K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hu : ‖(σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ}
    {A B : Matrix (Fin r) (Fin r) K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G)
    (hAn : ‖A‖ < (ℓ : ℝ)⁻¹) (hBn : ‖B‖ < (ℓ : ℝ)⁻¹)
    (hBG : ∀ g ∈ G, Commute B (g : Matrix (Fin r) (Fin r) K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) = A + B)
    {z : (Matrix (Fin r) (Fin r) K)ˣ} (hz : (z : Matrix (Fin r) (Fin r) K) = exp B)
    (k i : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hTz : ∀ c, (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
      (compoundMonoidHom k (z : Matrix (Fin r) (Fin r) K))).charpoly.IsRoot c → ‖ι c‖ ≤ T)
    (ζ : ℂ)
    (hζ : ((LinearMap.charpoly (coinvariantsFrobenius H
      (tensorPowerRepresentation (exteriorPowerRepresentation k ρ) i) φ)).map
        (ι.comp (algebraMap ℚ_[ℓ] K))).IsRoot ζ) :
    ‖ζ‖ ^ (κ * ℓ ^ N) ≤ T ^ i := by
  classical
  set τ := tensorPowerRepresentation (exteriorPowerRepresentation k ρ) i
  set X : Matrix (Fin r) (Fin r) K →* _ := extTensorHom (R := K) (r := r) k i
  set Pi0 : Matrix (Fin r) (Fin r) K := (P₀ : Matrix (Fin r) (Fin r) K)
  set Pi1 : Matrix (Fin r) (Fin r) K :=
    ((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K)
  set ρK : Γ → Matrix (Fin r) (Fin r) K :=
    fun g => (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K)
  set ρt : Γ → Matrix (Fin r) (Fin r) K := fun g => Pi1 * ρK g * Pi0
  have h01 : Pi0 * Pi1 = 1 := Units.mul_inv P₀
  have h10 : Pi1 * Pi0 = 1 := Units.inv_mul P₀
  set f := coinvariantsFrobenius H τ φ
  have hmon := LinearMap.charpoly_monic f
  have hroots : ((f.charpoly.map (algebraMap ℚ_[ℓ] K)).map ι).roots =
      (f.charpoly.map (algebraMap ℚ_[ℓ] K)).roots.map ι :=
    ((hmon.map _).roots_map_of_card_eq_natDegree ι IsAlgClosed.card_roots_eq_natDegree).symm
  have hζ' : ζ ∈ ((f.charpoly.map (algebraMap ℚ_[ℓ] K)).map ι).roots := by
    rwa [Polynomial.map_map, Polynomial.mem_roots ((hmon.map _).ne_zero)]
  rw [hroots, Multiset.mem_map] at hζ'
  obtain ⟨μ, hμ, rfl⟩ := hζ'
  have hμroot : (f.charpoly.map (algebraMap ℚ_[ℓ] K)).IsRoot μ :=
    (Polynomial.mem_roots ((hmon.map _).ne_zero)).mp hμ
  obtain ⟨v, hv0, hvH, hvφ⟩ := exists_vecMul_eq_of_isRoot_coinvariantsFrobenius H τ φ hμroot
  have hτ : ∀ g, (τ g : Matrix _ _ ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) = X (ρK g) := by
    intro g
    rw [tensorPowerRepresentation_exteriorPowerRepresentation_val, extTensorHom_map]
  have hconj : ∀ g, X (ρK g) * X Pi0 = X Pi0 * X (ρt g) := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [ρt, ← Matrix.mul_assoc, h01, Matrix.one_mul]
  set v' := v ᵥ* X Pi0
  have hv'0 : v' ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (· ᵥ* X Pi1) h
    simpa only [v', Matrix.vecMul_vecMul, ← map_mul, h01, map_one, Matrix.vecMul_one,
      Matrix.zero_vecMul] using this
  have hv'g : ∀ (g : Γ) (c : K), v ᵥ* X (ρK g) = c • v → v' ᵥ* X (ρt g) = c • v' := by
    intro g c hc
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hc, Matrix.smul_vecMul]
  obtain ⟨w, hw0, hw⟩ := exists_vecMul_gradedDiag_eq (d := extTensorGrading k i d)
    (T := fun a : Option H => X (ρt (a.elim φ fun h => (h : Γ))))
    (c := fun a : Option H => a.elim μ fun _ => 1)
    (fun a => IsGradedUpper.extTensorHom k i (hup _)) hv'0 (fun a => by
      cases a with
      | none => exact hv'g φ μ (by rw [← hτ]; exact hvφ)
      | some h => exact hv'g h 1 (by rw [← hτ, one_smul]; exact hvH h h.2))
  have hdiag : ∀ g, gradedDiag (extTensorGrading k i d) (X (ρt g)) = X (σ' g : Matrix _ _ K) := by
    intro g
    rw [gradedDiag_extTensorHom k i (hup g), hσ']
  have hwH : ∀ h ∈ H, w ᵥ* X (σ' h : Matrix _ _ K) = w := by
    intro h hh
    simpa only [hdiag, Option.elim, one_smul] using hw (some ⟨h, hh⟩)
  have hwφ : w ᵥ* X (σ' φ : Matrix _ _ K) = μ • w := by
    have := hw none
    rwa [hdiag] at this
  have hXσ : ∀ g g', X (σ' (g * g') : Matrix _ _ K) =
      X (σ' g : Matrix _ _ K) * X (σ' g' : Matrix _ _ K) := by
    intro g g'
    rw [map_mul, Units.val_mul, map_mul]
  have h1 : w ᵥ* (X (σ' φ : Matrix _ _ K) * X (σ' φ⁻¹ : Matrix _ _ K)) = w := by
    rw [← hXσ, mul_inv_cancel, map_one, Units.val_one, map_one, Matrix.vecMul_one]
  obtain ⟨hμ0, hwφinv⟩ := vecMul_eq_inv_smul_of_vecMul_mul_eq hw0 h1 hwφ
  have hwpow : ∀ n : ℕ, w ᵥ* X (σ' (φ⁻¹ ^ n) : Matrix _ _ K) = μ⁻¹ ^ n • w := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one, Units.val_one, map_one, Matrix.vecMul_one, pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ, hXσ, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, hwφinv, smul_smul,
        pow_succ]
  set C := dualExtTensorConstruction (ℓ := ℓ) (K := K) (r := r) k i
  have hCR : ∀ x : (Matrix (Fin r) (Fin r) K)ˣ, (C.R x : Matrix _ _ K) *ᵥ w =
      w ᵥ* X ((x⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix _ _ K) := by
    intro x
    rw [dualExtTensorConstruction_R, Matrix.mulVec_transpose]
  have hGv : ∀ g ∈ G, (C.R g : Matrix _ _ K) *ᵥ w = w := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := hGH g hg
    rw [hCR, ← map_inv]
    exact hwH _ (H.inv_mem hh)
  have huv : (C.R (σ' (φ ^ κ)) : Matrix _ _ K) *ᵥ w = μ⁻¹ ^ κ • w := by
    rw [hCR, ← map_inv, ← inv_pow]
    exact hwpow κ
  have hzw := C.mulVec_eq_of_invariant hG hu hA hAn hBn hBG hAB hsum hz hw0 hGv huv
  rw [hCR] at hzw
  have hXz : w ᵥ* X (z : Matrix _ _ K) = ((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹ • w := by
    refine (vecMul_eq_inv_smul_of_vecMul_mul_eq hw0 ?_ hzw).2
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, Matrix.vecMul_one]
  have heig : (X (z : Matrix _ _ K)).charpoly.IsRoot (((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹) := by
    rw [← Matrix.charpoly_transpose, ← Matrix.charpoly_toLin',
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hbound := norm_le_pow_of_isRoot_charpoly_kronPowMatrix ι hT hTz i _ heig
  have hval : ((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹ = μ ^ (κ * ℓ ^ N) := by
    rw [← pow_mul, inv_pow, inv_inv]
  rwa [hval, map_pow, norm_pow] at hbound

end Main

end Stacks.EtaleCohomology

end
