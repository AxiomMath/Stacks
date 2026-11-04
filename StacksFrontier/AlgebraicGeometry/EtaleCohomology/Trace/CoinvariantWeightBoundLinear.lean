module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantWeightBound

/-!
# The coinvariant weight bound with coefficients in any field

`Stacks.EtaleCohomology.norm_pow_le_of_isRoot_coinvariantsFrobenius` (Weil II 1.5.2, the `H²_c`
term; Kedlaya, *Fourier transforms and p-adic Weil II*, Lemma 6.5.1) for a representation
`ρ : Γ → GL_r(F)` with coefficients in an arbitrary field `F` with an algebra structure towards the
complete field `K` of the block form, instead of `ℚ_ℓ`. This is the `E`-linear form used for
Weil II 1.5.1 with coefficients in a finite extension `E` of `ℚ_ℓ`
(`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock_linear`): the restriction of
scalars `Res_{E/ℚ_ℓ}` does not carry the `ι'`-reality of an `E`-linear representation, so the
argument is run with base field `E`.

## Main results

* `Stacks.EtaleCohomology.norm_pow_le_of_isRoot_coinvariantsFrobenius_linear`.
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
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra F K]
  {Γ : Type*} [Group Γ] {r : ℕ}

/-- **The Frobenius eigenvalues on the geometric coinvariants of `(⋀ᵏ ρ)^{⊗ i}` are bounded by the
determinantal weights**, for `ρ` with coefficients in any field `F` with a map to `K` (Weil II
1.5.2, the `H²_c` term; Kedlaya, Lemma 6.5.1). The case `F = ℚ_ℓ` is
`Stacks.EtaleCohomology.norm_pow_le_of_isRoot_coinvariantsFrobenius`. -/
public theorem norm_pow_le_of_isRoot_coinvariantsFrobenius_linear (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (ρ : Γ →* GL (Fin r) F) (P₀ : (Matrix (Fin r) (Fin r) K)ˣ)
    (d : Fin r → ℤ) (σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσ' : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d
      (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
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
        (ι.comp (algebraMap F K))).IsRoot ζ) :
    ‖ζ‖ ^ (κ * ℓ ^ N) ≤ T ^ i := by
  classical
  set τ := tensorPowerRepresentation (exteriorPowerRepresentation k ρ) i
  set X : Matrix (Fin r) (Fin r) K →* _ := extTensorHom (R := K) (r := r) k i
  set Pi0 : Matrix (Fin r) (Fin r) K := (P₀ : Matrix (Fin r) (Fin r) K)
  set Pi1 : Matrix (Fin r) (Fin r) K :=
    ((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K)
  set ρK : Γ → Matrix (Fin r) (Fin r) K :=
    fun g => (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K)
  set ρt : Γ → Matrix (Fin r) (Fin r) K := fun g => Pi1 * ρK g * Pi0
  have h01 : Pi0 * Pi1 = 1 := Units.mul_inv P₀
  have h10 : Pi1 * Pi0 = 1 := Units.inv_mul P₀
  -- step 1: a root in `K`
  set f := coinvariantsFrobenius H τ φ
  have hmon := LinearMap.charpoly_monic f
  have hroots : ((f.charpoly.map (algebraMap F K)).map ι).roots =
      (f.charpoly.map (algebraMap F K)).roots.map ι :=
    ((hmon.map _).roots_map_of_card_eq_natDegree ι IsAlgClosed.card_roots_eq_natDegree).symm
  have hζ' : ζ ∈ ((f.charpoly.map (algebraMap F K)).map ι).roots := by
    rw [Polynomial.map_map, Polynomial.mem_roots ((hmon.map _).ne_zero)]
    exact hζ
  rw [hroots, Multiset.mem_map] at hζ'
  obtain ⟨μ, hμ, rfl⟩ := hζ'
  have hμroot : (f.charpoly.map (algebraMap F K)).IsRoot μ :=
    (Polynomial.mem_roots ((hmon.map _).ne_zero)).mp hμ
  -- step 2: an invariant left eigenvector
  obtain ⟨v, hv0, hvH, hvφ⟩ := exists_vecMul_eq_of_isRoot_coinvariantsFrobenius H τ φ hμroot
  have hτ : ∀ g, (τ g : Matrix _ _ F).map (algebraMap F K) = X (ρK g) := by
    intro g
    rw [tensorPowerRepresentation_exteriorPowerRepresentation_val, extTensorHom_map]
  have hconj : ∀ g, X (ρK g) * X Pi0 = X Pi0 * X (ρt g) := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [ρt, ← Matrix.mul_assoc, h01, Matrix.one_mul]
  -- step 3: conjugate by `P₀`
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
  -- step 4: the lowest-grade part
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
    have := hw (some ⟨h, hh⟩)
    simp only [hdiag, Option.elim, one_smul] at this
    exact this
  have hwφ : w ᵥ* X (σ' φ : Matrix _ _ K) = μ • w := by
    have := hw none
    rwa [hdiag] at this
  -- `X ∘ σ'` on the left eigenvector
  have hXσ : ∀ g g', X (σ' (g * g') : Matrix _ _ K) =
      X (σ' g : Matrix _ _ K) * X (σ' g' : Matrix _ _ K) := by
    intro g g'
    rw [map_mul, Units.val_mul, map_mul]
  -- a left eigenvector for `a` with eigenvalue `c` is one for a right inverse of `a`, with `c⁻¹`
  have hinv : ∀ (a b : Matrix _ _ K) (c : K), a * b = 1 → w ᵥ* a = c • w →
      c ≠ 0 ∧ w ᵥ* b = c⁻¹ • w := by
    intro a b c hab h
    have h1 : c • (w ᵥ* b) = w := by
      rw [← Matrix.smul_vecMul, ← h, Matrix.vecMul_vecMul, hab, Matrix.vecMul_one]
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw0 (by simpa using h1.symm)
    exact ⟨hc, (eq_inv_smul_iff₀ hc).mpr h1⟩
  obtain ⟨hμ0, hwφinv⟩ := hinv (X (σ' φ : Matrix _ _ K)) (X (σ' φ⁻¹ : Matrix _ _ K)) μ
    (by rw [← hXσ, mul_inv_cancel, map_one, Units.val_one, map_one]) hwφ
  have hwpow : ∀ n : ℕ, w ᵥ* X (σ' (φ⁻¹ ^ n) : Matrix _ _ K) = μ⁻¹ ^ n • w := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one, Units.val_one, map_one, Matrix.vecMul_one, pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ, hXσ, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, hwφinv, smul_smul,
        pow_succ]
  -- step 5: the invariant vector of the dual construction
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
  -- step 6: `μ ^ (κ ℓ ^ N)` is an eigenvalue of `X z`
  have hXz : w ᵥ* X (z : Matrix _ _ K) = ((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹ • w :=
    (hinv _ _ _ (by rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
      hzw).2
  have heig : (X (z : Matrix _ _ K)).charpoly.IsRoot (((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹) := by
    rw [← Matrix.charpoly_transpose, ← Matrix.charpoly_toLin',
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    exact hXz
  have hbound := norm_le_pow_of_isRoot_charpoly_kronPowMatrix ι hT hTz i _ heig
  have hval : ((μ⁻¹ ^ κ) ^ ℓ ^ N)⁻¹ = μ ^ (κ * ℓ ^ N) := by
    rw [← pow_mul, inv_pow, inv_inv]
  rw [hval, map_pow, norm_pow] at hbound
  exact hbound


end Stacks.EtaleCohomology

end
