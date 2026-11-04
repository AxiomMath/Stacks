module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Algebra.Module.Projective

/-!
# Eigenvalues of Frobenius on coinvariants as left eigenvectors

Let `τ : Γ → GL_m(F)` be a matrix representation, `H ⊴ Γ` and `φ ∈ Γ`.  A root `z`, in an
algebraically closed extension `K` of `F`, of the characteristic polynomial of `φ` on the
`H`-coinvariants of `τ` is the eigenvalue of a nonzero row vector `v ∈ K^m` which is fixed by
`τ(H)`: `v τ(h) = v` for `h ∈ H` and `v τ(φ) = z v`. Consequently, if `g ∈ φ ^ d H`, then `z ^ d`
is a root of the characteristic polynomial of `τ(g)`.

## Main results

* `Stacks.EtaleCohomology.exists_vecMul_eq_of_isRoot_coinvariantsFrobenius`: a root of the
  characteristic polynomial of `φ` on the coinvariants is the eigenvalue of an `H`-invariant row
  vector.
* `Stacks.EtaleCohomology.isRoot_charpoly_pow_of_isRoot_coinvariantsFrobenius`: for `g ∈ φ ^ d H`,
  the `d`-th power of such a root is a root of the characteristic polynomial of `τ(g)`.
-/

@[expose] public noncomputable section

open Polynomial Matrix

namespace Stacks.EtaleCohomology

variable {Γ : Type*} [Group Γ] {F : Type*} [Field F] {m : ℕ} (H : Subgroup Γ) [H.Normal]

/-- Mapping a product of matrices along a ring homomorphism commutes with row-vector action. -/
private theorem vecMul_map_mul {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) {l n o : Type*}
    [Fintype l] [Fintype n] (v : l → S) (A : Matrix l n R) (B : Matrix n o R) :
    v ᵥ* (A * B).map f = (v ᵥ* A.map f) ᵥ* B.map f := by
  rw [Matrix.map_mul, Matrix.vecMul_vecMul]

/-- If `z ∈ K` is a root of the characteristic polynomial of `φ` acting on the `H`-coinvariants of
`τ`, then there is a nonzero row vector `v ∈ K^m` with `v τ(h) = v` for all `h ∈ H` and
`v τ(φ) = z v`. -/
public theorem exists_vecMul_eq_of_isRoot_coinvariantsFrobenius {K : Type*} [Field K]
    [Algebra F K] (τ : Γ →* GL (Fin m) F) (φ : Γ) {z : K}
    (hz : ((LinearMap.charpoly (coinvariantsFrobenius H τ φ)).map (algebraMap F K)).IsRoot z) :
    ∃ v : Fin m → K, v ≠ 0 ∧
      (∀ h ∈ H, v ᵥ* (τ h : Matrix (Fin m) (Fin m) F).map (algebraMap F K) = v) ∧
      v ᵥ* (τ φ : Matrix (Fin m) (Fin m) F).map (algebraMap F K) = z • v := by
  classical
  set ρH : Representation F H (Fin m → F) := (matrixRepresentation τ).comp H.subtype
  set Q := Representation.Coinvariants ρH
  set mk : (Fin m → F) →ₗ[F] Q := Representation.Coinvariants.mk ρH
  set f := coinvariantsFrobenius H τ φ
  set b := Module.finBasis F Q
  set M := LinearMap.toMatrix b b f
  set Pm : Matrix (Fin (Module.finrank F Q)) (Fin m) F := LinearMap.toMatrix (Pi.basisFun F _) b mk
  have hmkH : ∀ h ∈ H, mk ∘ₗ Matrix.toLin' (τ h : Matrix (Fin m) (Fin m) F) = mk := fun h hh =>
    LinearMap.ext (Representation.Coinvariants.mk_self_apply ρH ⟨h, hh⟩)
  have hmkφ : f ∘ₗ mk = mk ∘ₗ Matrix.toLin' (τ φ : Matrix (Fin m) (Fin m) F) := rfl
  have hPH : ∀ h ∈ H, Pm * (τ h : Matrix (Fin m) (Fin m) F) = Pm := by
    intro h hh
    have := congrArg (LinearMap.toMatrix (Pi.basisFun F _) b) (hmkH h hh)
    rwa [LinearMap.toMatrix_comp _ (Pi.basisFun F _), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin'] at this
  have hPφ : M * Pm = Pm * (τ φ : Matrix (Fin m) (Fin m) F) := by
    have := congrArg (LinearMap.toMatrix (Pi.basisFun F _) b) hmkφ
    rwa [LinearMap.toMatrix_comp _ b, LinearMap.toMatrix_comp _ (Pi.basisFun F _),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at this
  obtain ⟨s, hs⟩ := mk.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Representation.Coinvariants.mk_surjective ρH))
  set S : Matrix (Fin m) (Fin (Module.finrank F Q)) F := LinearMap.toMatrix b (Pi.basisFun F _) s
  have hPS : Pm * S = 1 := by
    have := congrArg (LinearMap.toMatrix b b) hs
    rwa [LinearMap.toMatrix_comp _ (Pi.basisFun F _), LinearMap.toMatrix_id] at this
  have hroot : ((M.map (algebraMap F K))ᵀ).charpoly.IsRoot z := by
    rwa [Matrix.charpoly_transpose, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hroot
  obtain ⟨w, hw⟩ := hroot.exists_hasEigenvector
  have hw' : w ᵥ* M.map (algebraMap F K) = z • w := by
    rw [← Matrix.mulVec_transpose, ← Matrix.toLin'_apply]
    exact hw.apply_eq_smul
  refine ⟨w ᵥ* Pm.map (algebraMap F K), ?_, fun h hh => ?_, ?_⟩
  · intro h0
    have := congrArg (· ᵥ* S.map (algebraMap F K)) h0
    rw [← vecMul_map_mul, hPS, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one,
      Matrix.zero_vecMul] at this
    exact hw.2 this
  · rw [← vecMul_map_mul, hPH h hh]
  · rw [← vecMul_map_mul, ← hPφ, vecMul_map_mul, hw', Matrix.smul_vecMul]

/-- If `g ∈ φ ^ d H`, then for every root `z` along `ι` of the characteristic polynomial of `φ` on
the `H`-coinvariants of `τ`, `z ^ d` is a root along `ι` of the characteristic polynomial of
`τ g`. -/
public theorem isRoot_charpoly_pow_of_isRoot_coinvariantsFrobenius (ι : F →+* ℂ)
    (τ : Γ →* GL (Fin m) F) (φ : Γ) {g : Γ} {d : ℕ} (hg : (φ ^ d)⁻¹ * g ∈ H) {z : ℂ}
    (hz : ((LinearMap.charpoly (coinvariantsFrobenius H τ φ)).map ι).IsRoot z) :
    (((τ g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).charpoly.map ι).IsRoot (z ^ d) := by
  classical
  let : Algebra F ℂ := ι.toAlgebra
  obtain ⟨v, hv0, hvH, hvφ⟩ := exists_vecMul_eq_of_isRoot_coinvariantsFrobenius (K := ℂ) H τ φ hz
  have hpow : ∀ k : ℕ, v ᵥ* (τ (φ ^ k) : Matrix (Fin m) (Fin m) F).map ι = z ^ k • v := by
    intro k
    induction k with
    | zero => simp [Matrix.map_one _ (map_zero ι) (map_one ι)]
    | succ k ih =>
      rw [pow_succ, map_mul, Units.val_mul, vecMul_map_mul, ih, Matrix.smul_vecMul]
      show z ^ k • (v ᵥ* (τ φ : Matrix (Fin m) (Fin m) F).map (algebraMap F ℂ)) = _
      rw [hvφ, smul_smul, pow_succ]
  have hgv : v ᵥ* (τ g : Matrix (Fin m) (Fin m) F).map ι = z ^ d • v := by
    have hg' : g = φ ^ d * ((φ ^ d)⁻¹ * g) := by group
    rw [hg', map_mul, Units.val_mul, vecMul_map_mul, hpow, Matrix.smul_vecMul]
    exact congrArg _ (hvH _ hg)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose,
    ← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply,
    Matrix.mulVec_transpose]
  exact ⟨hgv, hv0⟩

end Stacks.EtaleCohomology

end
