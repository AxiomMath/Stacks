module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixWeakBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact

/-!
# The weights of the Frobenius on the inertia invariants

For `ρ : G → GL_r(E)` and a subgroup `H` of `G` normalized by `F ∈ G`, the `E`-subspace
`(E^r)^H` of `H`-invariants is stable under `ρ(F)`. A root `z` of the characteristic polynomial
of `ρ(F)` restricted to it, read along `ι' : E → ℂ`, is the eigenvalue of an eigenvector in `ℂ^r`
of `ι' ρ(F)` fixed by `ι' ρ(H)`: the columns of a basis of `(E^r)^H` map it to such a vector.
Weil II 1.8.4 (`Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_weakInertiaBound`) therefore
says that the restriction of the geometric Frobenius to the inertia invariants is mixed of integer
weights `≤ w`, in the form `Stacks.EtaleCohomology.IsCharpolyNormMixedOfWeightLE`.

## Main results

* `Stacks.EtaleCohomology.exists_mulVec_map_eq_smul_of_isRoot_charpoly_restrict`: eigenvectors of
  a restriction to a stable subspace, read along a field embedding.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_invariants_of_weakInertiaBound`: the
  Frobenius on the inertia invariants is mixed of weights `≤ w`.
-/

@[expose] public noncomputable section

open Matrix
open scoped Pointwise

namespace Stacks.EtaleCohomology

section LinearAlgebra

variable {K : Type*} [Field K] (ι : K →+* ℂ) {n : ℕ}

/-- A left inverse stays a left inverse after mapping along a field embedding. -/
private theorem map_mulVec_map_mulVec_of_mul_eq_one {k m : ℕ} {D : Matrix (Fin k) (Fin m) K}
    {C : Matrix (Fin m) (Fin k) K} (h : D * C = 1) (y : Fin k → ℂ) :
    D.map ι *ᵥ (C.map ι *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero ι) (map_one ι),
    Matrix.one_mulVec]

/-- Applying mapped matrices in turn is applying the mapped product. -/
private theorem map_mulVec_map_mulVec {k m p : ℕ} (A : Matrix (Fin k) (Fin m) K)
    (B : Matrix (Fin m) (Fin p) K) (y : Fin p → ℂ) :
    A.map ι *ᵥ (B.map ι *ᵥ y) = (A * B).map ι *ᵥ y := by
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

/-- **Matrices of a restriction.**  For `Z ⊆ K^n` stable under `M`, there are `C : K^k → K^n`
with image `Z` and left inverse `D`, and the matrix `B` of `M|_Z` in the corresponding basis:
`M C = C B`, `D C = 1`, `C D x = x` on `Z`, and `charpoly B = charpoly (M|_Z)`. -/
public theorem exists_restrict_basisMatrix (M : Matrix (Fin n) (Fin n) K)
    (Z : Submodule K (Fin n → K)) (hZ : ∀ v ∈ Z, Matrix.toLin' M v ∈ Z) :
    ∃ (k : ℕ) (C : Matrix (Fin n) (Fin k) K) (D : Matrix (Fin k) (Fin n) K)
      (B : Matrix (Fin k) (Fin k) K), M * C = C * B ∧ D * C = 1 ∧
      (∀ x ∈ Z, C *ᵥ (D *ᵥ x) = x) ∧ (∀ u, C *ᵥ u ∈ Z) ∧
      B.charpoly = ((Matrix.toLin' M).restrict hZ).charpoly := by
  classical
  set f := (Matrix.toLin' M).restrict hZ with hf
  set k := Module.finrank K Z
  let bZ : Module.Basis (Fin k) K Z := Module.finBasis K Z
  set B := LinearMap.toMatrix bZ bZ f with hB
  let C : Matrix (Fin n) (Fin k) K := Matrix.of fun i j => (bZ j : Fin n → K) i
  have hCcol : ∀ u : Fin k → K, C *ᵥ u = ((bZ.equivFun.symm u : Z) : Fin n → K) := fun u => by
    funext i
    simp only [C, Matrix.mulVec, dotProduct, Matrix.of_apply, Module.Basis.equivFun_symm_apply,
      Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hMC : M * C = C * B := by
    ext i j
    have h1 : (M * C) i j = (M *ᵥ (bZ j : Fin n → K)) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, C, Matrix.of_apply]
    have h2 : M *ᵥ (bZ j : Fin n → K) = ((f (bZ j) : Z) : Fin n → K) := by
      rw [hf, LinearMap.restrict_coe_apply, Matrix.toLin'_apply]
    have h3 : (C * B) i j = (C *ᵥ fun l => B l j) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h4 : (fun l => B l j) = bZ.equivFun (f (bZ j)) := by
      funext l
      rw [hB, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]
    rw [h1, h2, h3, hCcol, h4, LinearEquiv.symm_apply_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective Z.subtype Z.ker_subtype
  have hgx : ∀ x : Z, g (x : Fin n → K) = x := fun x => by
    have := LinearMap.congr_fun hg x
    rwa [LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_subtype] at this
  let D : Matrix (Fin k) (Fin n) K := LinearMap.toMatrix' (bZ.equivFun.toLinearMap ∘ₗ g)
  have hDx : ∀ x : Fin n → K, D *ᵥ x = bZ.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', LinearMap.comp_apply, LinearEquiv.coe_coe]
  refine ⟨k, C, D, B, hMC, ?_, ?_, ?_, ?_⟩
  · refine Matrix.toLin'.injective ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    refine LinearMap.ext fun u => ?_
    rw [LinearMap.comp_apply, Matrix.toLin'_apply (M := C), hCcol, Matrix.toLin'_apply, hDx, hgx,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · intro x hx
    rw [hDx, hCcol, hgx ⟨x, hx⟩, LinearEquiv.symm_apply_apply]
  · intro u
    rw [hCcol]
    exact (bZ.equivFun.symm u).2
  · rw [hB, LinearMap.charpoly_toMatrix]

/-- A scalar matrix acts by scalar multiplication. -/
private theorem scalar_mulVec_eq_smul {k : ℕ} (z : ℂ) (u : Fin k → ℂ) :
    (Matrix.scalar (Fin k) z) *ᵥ u = z • u := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- A root of the characteristic polynomial of a square matrix over `ℂ` is an eigenvalue. -/
theorem exists_mulVec_eq_smul_of_isRoot_charpoly {k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ) (z : ℂ)
    (hz : B.charpoly.IsRoot z) : ∃ u : Fin k → ℂ, u ≠ 0 ∧ B *ᵥ u = z • u := by
  have hdet : (Matrix.scalar (Fin k) z - B).det = 0 := by
    rwa [← Matrix.eval_charpoly]
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨u, hu0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero, scalar_mulVec_eq_smul] at hu
  exact hu.symm

/-- An eigenvalue of a square matrix over `ℂ` is a root of its characteristic polynomial. -/
theorem isRoot_charpoly_of_mulVec_eq_smul {k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ) (z : ℂ)
    {u : Fin k → ℂ} (hu0 : u ≠ 0) (hu : B *ᵥ u = z • u) : B.charpoly.IsRoot z := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hu0, ?_⟩
  rw [Matrix.sub_mulVec, scalar_mulVec_eq_smul, hu, sub_self]

/-- **Eigenvectors of a restriction, along a field embedding.**  If `Z ⊆ K^n` is stable under
`M` and `z` is a root of the characteristic polynomial of `M|_Z` read along `ι`, then `ι M` has an
eigenvector `v ∈ ℂ^n` with eigenvalue `z` that is fixed by `ι M'` for every `M'` fixing `Z`
pointwise. -/
public theorem exists_mulVec_map_eq_smul_of_isRoot_charpoly_restrict
    (M : Matrix (Fin n) (Fin n) K) (Z : Submodule K (Fin n → K))
    (hZ : ∀ v ∈ Z, Matrix.toLin' M v ∈ Z) (z : ℂ)
    (hz : (((Matrix.toLin' M).restrict hZ).charpoly.map ι).IsRoot z) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ M.map ι *ᵥ v = z • v ∧
      ∀ M' : Matrix (Fin n) (Fin n) K, (∀ x ∈ Z, M' *ᵥ x = x) → M'.map ι *ᵥ v = v := by
  obtain ⟨k, C, D, B, hMC, hDC, -, hCZ, hB⟩ := exists_restrict_basisMatrix M Z hZ
  obtain ⟨u, hu0, hBu⟩ := exists_mulVec_eq_smul_of_isRoot_charpoly (B.map ι) z (by
    rwa [Matrix.charpoly_map, hB])
  refine ⟨C.map ι *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu0
    rw [← map_mulVec_map_mulVec_of_mul_eq_one ι hDC u, h0, Matrix.mulVec_zero]
  · rw [map_mulVec_map_mulVec, hMC, ← map_mulVec_map_mulVec, hBu, Matrix.mulVec_smul]
  · intro M' hM'
    have hM'C : M' * C = C := by
      refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      exact hM' _ (hCZ u)
    rw [map_mulVec_map_mulVec, hM'C]

/-- **Kernel inclusions persist along field embeddings, for rectangular matrices.** -/
theorem mulVec_map_eq_zero_of_forall_mulVec_eq_zero_rect {L : Type*} [Field L] (ι : K →+* L)
    {m p : Type*} [Finite m] [Finite p] {A : Matrix m (Fin n) K} {B : Matrix p (Fin n) K}
    (h : ∀ v : Fin n → K, A *ᵥ v = 0 → B *ᵥ v = 0) (w : Fin n → L) (hw : A.map ι *ᵥ w = 0) :
    B.map ι *ᵥ w = 0 := by
  classical
  have := Fintype.ofFinite m
  have hrow : ∀ i : p, ∃ ψ : (m → K) →ₗ[K] K, ∀ y, ψ (A *ᵥ y) = (B *ᵥ y) i := by
    intro i
    refine exists_comp_eq_of_ker_le (g := Matrix.mulVecLin A)
      (f := (LinearMap.proj i).comp (Matrix.mulVecLin B)) fun y hy => ?_
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    simp [h y hy]
  choose ψ hψ using hrow
  let C : Matrix p m K := LinearMap.toMatrix' (LinearMap.pi ψ)
  have hBC : B = C * A := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    funext i
    rw [LinearMap.pi_apply, hψ i y]
  rw [hBC, Matrix.map_mul, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]

/-- **Fixed eigenvectors over `ℂ` give roots of the restricted characteristic polynomial.**  Let
`Z ⊆ K^n` be the vectors fixed by a family `Mⱼ`, stable under `M`.  If `v ∈ ℂ^n` is nonzero, fixed
by every `ι Mⱼ`, and `ι M v = μ v`, then `μ` is a root of the characteristic polynomial of `M|_Z`
read along `ι`. -/
public theorem isRoot_charpoly_restrict_of_mulVec_map_eq_smul (M : Matrix (Fin n) (Fin n) K)
    {J : Type*} (Ms : J → Matrix (Fin n) (Fin n) K) (Z : Submodule K (Fin n → K))
    (hZdef : ∀ x, x ∈ Z ↔ ∀ j, Ms j *ᵥ x = x) (hZ : ∀ v ∈ Z, Matrix.toLin' M v ∈ Z)
    {v : Fin n → ℂ} (hv0 : v ≠ 0) (hvfix : ∀ j, (Ms j).map ι *ᵥ v = v) {μ : ℂ}
    (hv : M.map ι *ᵥ v = μ • v) :
    (((Matrix.toLin' M).restrict hZ).charpoly.map ι).IsRoot μ := by
  classical
  obtain ⟨k, C, D, B, hMC, hDC, hCD, -, hB⟩ := exists_restrict_basisMatrix M Z hZ
  let T : Finset J → Submodule K (Fin n → K) := fun s =>
    ⨅ j ∈ s, LinearMap.ker (Matrix.toLin' (Ms j) - LinearMap.id)
  have hmemT : ∀ s x, x ∈ T s ↔ ∀ j ∈ s, Ms j *ᵥ x = x := fun s x => by
    simp only [T, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := (wellFounded_lt (α := Submodule K (Fin n → K))).has_min
    (Set.range T) ⟨T ∅, ∅, rfl⟩
  have hfin : ∀ x, (∀ j ∈ s, Ms j *ᵥ x = x) → x ∈ Z := by
    intro x hx
    rw [hZdef]
    intro j
    have hle : T (insert j s) ≤ T s := fun y hy => (hmemT _ y).2 fun i hi =>
      (hmemT _ y).1 hy i (Finset.mem_insert_of_mem hi)
    have heq : T (insert j s) = T s := by
      by_contra hne
      exact hs _ ⟨_, rfl⟩ (lt_of_le_of_ne hle hne)
    have : x ∈ T (insert j s) := by rw [heq]; exact (hmemT s x).2 hx
    exact (hmemT _ x).1 this j (Finset.mem_insert_self j s)
  let A : Matrix (s × Fin n) (Fin n) K := Matrix.of fun p l => (Ms p.1 - 1) p.2 l
  have hA : ∀ x, A *ᵥ x = 0 → (1 - C * D) *ᵥ x = 0 := by
    intro x hx
    have hxZ : x ∈ Z := hfin x fun j hj => by
      have := fun i => congrFun hx (⟨j, hj⟩, i)
      have h' : (Ms j - 1) *ᵥ x = 0 := funext fun i => by
        simpa [A, Matrix.mulVec, dotProduct] using this i
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h'
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hCD x hxZ, sub_self]
  have hAv : A.map ι *ᵥ v = 0 := by
    funext p
    have := congrFun (hvfix p.1) p.2
    have h' : ((Ms p.1 - 1).map ι *ᵥ v) p.2 = 0 := by
      rw [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι),
        Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, this, sub_self]
    simpa [A, Matrix.mulVec, dotProduct] using h'
  have hv' := mulVec_map_eq_zero_of_forall_mulVec_eq_zero_rect ι hA v hAv
  rw [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero, Matrix.map_mul, ← Matrix.mulVec_mulVec] at hv'
  generalize D.map ι *ᵥ v = u at hv'
  have hu0 : u ≠ 0 := fun h0 => hv0 (by rw [hv', h0, Matrix.mulVec_zero])
  have hBu : B.map ι *ᵥ u = μ • u := by
    have h1 : C.map ι *ᵥ (B.map ι *ᵥ u) = C.map ι *ᵥ (μ • u) := by
      rw [map_mulVec_map_mulVec, ← hMC, ← map_mulVec_map_mulVec, Matrix.mulVec_smul, ← hv', hv]
    rw [← map_mulVec_map_mulVec_of_mul_eq_one ι hDC (B.map ι *ᵥ u), h1,
      map_mulVec_map_mulVec_of_mul_eq_one ι hDC]
  have := isRoot_charpoly_of_mulVec_eq_smul (B.map ι) μ hu0 hBu
  rwa [Matrix.charpoly_map, hB] at this

/-- **Roots along an injective intertwiner with a power.**  Let `ι : Z → H` be an injective
`K`-linear map with `ι ∘ T = f ^ d ∘ ι`, `d > 0`, between finite dimensional spaces.  If every root
of the characteristic polynomial of `f` read along `ι'` has absolute value at most `R ≥ 0`, so does
every root of that of `T`, with `R ^ d`. -/
public theorem norm_le_pow_of_isRoot_charpoly_of_injective {Z H : Type*} [AddCommGroup Z]
    [Module K Z] [FiniteDimensional K Z] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (T : Module.End K Z) (f : Module.End K H) (j : Z →ₗ[K] H) (hj : Function.Injective j)
    {d : ℕ} (hd : 0 < d) (hjT : j ∘ₗ T = (f ^ d) ∘ₗ j) {R : ℝ}
    (hf : ∀ z : ℂ, (f.charpoly.map ι).IsRoot z → ‖z‖ ≤ R) (z : ℂ)
    (hz : (T.charpoly.map ι).IsRoot z) : ‖z‖ ≤ R ^ d := by
  classical
  let bZ := Module.finBasis K Z
  let bH := Module.finBasis K H
  set B := LinearMap.toMatrix bZ bZ T with hB
  set P := LinearMap.toMatrix bH bH f with hP
  set J := LinearMap.toMatrix bZ bH j with hJ
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  set D := LinearMap.toMatrix bH bZ g with hD
  have hDJ : D * J = 1 := by
    rw [hD, hJ, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have hPJ : P ^ d * J = J * B := by
    rw [hP, hJ, hB, LinearMap.toMatrix_pow, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      hjT]
  obtain ⟨u, hu0, hBu⟩ := exists_mulVec_eq_smul_of_isRoot_charpoly (B.map ι) z (by
    rwa [Matrix.charpoly_map, hB, LinearMap.charpoly_toMatrix])
  have hv0 : J.map ι *ᵥ u ≠ 0 := fun h0 =>
    hu0 (by rw [← map_mulVec_map_mulVec_of_mul_eq_one ι hDJ u, h0, Matrix.mulVec_zero])
  have hpow : (P.map ι) ^ d *ᵥ (J.map ι *ᵥ u) = z • (J.map ι *ᵥ u) := by
    have hmap : (P.map ι) ^ d = (P ^ d).map ι := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
    rw [hmap, map_mulVec_map_mulVec, hPJ, ← map_mulVec_map_mulVec, hBu, Matrix.mulVec_smul]
  obtain ⟨η, -, hη0, μ, hPη, hμ⟩ := exists_mulVec_eq_smul_pow_eq_of_pow_mulVec_eq_smul (P.map ι) ⊤
    (fun _ _ => Submodule.mem_top) Submodule.mem_top hv0 hd hpow
  have hμR : ‖μ‖ ≤ R := by
    refine hf μ ?_
    have := isRoot_charpoly_of_mulVec_eq_smul (P.map ι) μ hη0 hPη
    rwa [Matrix.charpoly_map, hP, LinearMap.charpoly_toMatrix] at this
  rw [← hμ, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg μ) hμR d

end LinearAlgebra

section Invariants

variable {G : Type*} [Group G] {E : Type*} [Field E] {r : ℕ}

/-- **An element of the normalizer of `H` preserves the `H`-invariants.** -/
public theorem toLin'_mem_invariants_of_mem_normalizer (ρ : G →* GL (Fin r) E) (H : Subgroup G)
    {F : G} (hF : F ∈ Subgroup.normalizer (H : Set G)) :
    ∀ v ∈ Representation.invariants ((matrixRepresentation ρ).comp H.subtype),
      Matrix.toLin' ((ρ F : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) v ∈
        Representation.invariants ((matrixRepresentation ρ).comp H.subtype) := by
  intro v hv h
  have hFh : F⁻¹ * (h : G) * F ∈ H := (Subgroup.mem_normalizer_iff''.1 hF h).1 h.2
  have := hv ⟨_, hFh⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, matrixRepresentation_apply] at this ⊢
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul,
    show (h : G) * F = F * (F⁻¹ * h * F) by group, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    this]

end Invariants

section Weights

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L] [Algebra A L] [IsScalarTower A K L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {Y : Type*} {Frob : Y → G} {deg : Y → ℕ} {q₀ : ℝ} {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Weil II, Théorème 1.8.4, on the `E`-subspace of inertia invariants.**  Let `ρ : G → GL_r(E)`
be pure of the integer weight `w` along `ι'` at the `Frob y`, with `Res_b ρ` continuous, and assume
the weak estimate.  Then the geometric Frobenius `ρ(φ Fr⁻¹)` restricted to the `E`-subspace of
`(E^r)` of `φ(I)`-invariants is mixed of integer weights `≤ w` along `ι'`, for `q` the order of the
residue field: every root `z` of its characteristic polynomial satisfies `|z| = q ^ (w' / 2)` with
`w' ≤ w` an integer. -/
public theorem isCharpolyNormMixedOfWeightLE_invariants_of_weakInertiaBound
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) (φ : Gal(L/K) →* G) (hφ : Continuous φ)
    {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {r : ℕ}
    (ρ : G →* GL (Fin r) E) (hρ : Continuous (restrictScalarsRep b ρ)) (ι' : E →+* ℂ)
    (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (hFr : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (hq₀ : 0 < q₀) (w : ℤ)
    (hpure : ∀ (y : Y) (z : ℂ), (((ρ (Frob y) : GL (Fin r) E) :
      Matrix (Fin r) (Fin r) E).charpoly.map ι').IsRoot z → ‖z‖ = q₀ ^ ((deg y : ℝ) * w / 2))
    (hweak : WeakInertiaBound A K L P Frob deg q₀ φ Fr E b ι') :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    IsCharpolyNormMixedOfWeightLE (Nat.card (IsLocalRing.ResidueField A)) ι' w
      ((Matrix.toLin' ((ρ (φ Fr⁻¹) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer ρ ((P.inertia Gal(L/K)).map φ)
          (map_inv_mem_normalizer_map_inertia A K L P φ Fr hFrD))) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField A) : ℝ) with hq_def
  have hq : 0 < q := by rw [hq_def]; exact_mod_cast Nat.card_pos
  intro z hz
  obtain ⟨v, hv0, hvF, hvfix⟩ := exists_mulVec_map_eq_smul_of_isRoot_charpoly_restrict ι' _ _ _ z hz
  have hvI : ∀ σ ∈ P.inertia Gal(L/K),
      ((ρ (φ σ) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map ι' *ᵥ v = v := fun σ hσ =>
    hvfix _ fun x hx => hx ⟨φ σ, σ, hσ, rfl⟩
  obtain ⟨i, hi⟩ := exists_norm_sq_mul_pow_eq_of_weakInertiaBound A K L P hℓ φ hφ b ρ hρ ι' Fr
    hFrD hFr hq₀ w hpure hweak hv0 hvI hvF
  refine ⟨w - i, by omega, ?_⟩
  have hqi : (0 : ℝ) < q ^ i := pow_pos hq i
  have e1 : ‖z‖ ^ 2 = q ^ (w : ℝ) / q ^ i := by
    rw [← hi, mul_div_cancel_right₀ _ hqi.ne']
  have e2 : (q ^ (((w - i : ℤ) : ℝ) / 2)) ^ 2 = q ^ (w : ℝ) / q ^ i := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q i,
      ← Real.rpow_sub hq]
    congr 1
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq.le _) two_ne_zero).1 (e1.trans e2.symm)

/-- **The weak estimate from its `E`-linear form**: it suffices to bound, along `ι'`, the roots of
the characteristic polynomial of `τ(φ Fr⁻¹)` restricted to the `E`-subspace of `φ(I)`-invariants,
for every `τ` mixed of weights `≤ w'`, by `q ^ ((w' + 2) / 2)`. -/
public theorem weakInertiaBound_of_forall_isRoot_charpoly_restrict (φ : Gal(L/K) →* G)
    {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
    (ι' : E →+* ℂ) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (h : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ (N : ℕ) (τ : G →* GL (Fin N) E), Continuous (restrictScalarsRep b τ) → ∀ w' : ℝ,
      IsFrobeniusMixedLE Frob deg q₀ ι' τ w' → ∀ z : ℂ,
      (((Matrix.toLin' ((τ (φ Fr⁻¹) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ ((P.inertia Gal(L/K)).map φ)
          (map_inv_mem_normalizer_map_inertia A K L P φ Fr hFrD))).charpoly.map ι').IsRoot z →
      ‖z‖ ≤ (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ ((w' + 2) / 2)) :
    WeakInertiaBound A K L P Frob deg q₀ φ Fr E b ι' := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro N τ hτ w' hmix Y hY hYfix μ hμ
  refine h N τ hτ w' hmix μ (isRoot_charpoly_restrict_of_mulVec_map_eq_smul ι' _
    (fun σ : (P.inertia Gal(L/K)) => ((τ (φ σ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) _
    (fun x => ?_) _ hY (fun σ => hYfix σ σ.2) hμ)
  constructor
  · intro hx σ
    exact hx ⟨φ σ, σ, σ.2, rfl⟩
  · rintro hx ⟨_, σ, hσ, rfl⟩
    exact hx ⟨σ, hσ⟩

end Weights

end Stacks.EtaleCohomology

end
