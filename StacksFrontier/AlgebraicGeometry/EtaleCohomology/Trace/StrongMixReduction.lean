module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixPlumbing
public import Mathlib.LinearAlgebra.Matrix.ToLin
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Eigenvalues of powers on stable subspaces

If `A` is a square complex matrix, `Z` an `A`-stable subspace and `ξ ∈ Z` a nonzero vector with
`A ^ F ξ = c ξ`, `F > 0`, then `A` has an eigenvector in `Z` whose eigenvalue `μ` satisfies
`μ ^ F = c`: the span of `ξ, A ξ, …, A ^ (F - 1) ξ` is `A`-stable, `A ^ F` acts on it by `c`,
and it contains an eigenvector of `A`.  In the reduction of Weil II 1.8.4 to the weak estimate,
this turns a bound on the eigenvalues of the Frobenius on the local invariants into one for its
powers.  The module also records Kronecker products and powers of vectors and the permutation
representation of a group acting on a finite set.

## Main results

* `Stacks.EtaleCohomology.exists_mulVec_eq_smul_pow_eq_of_pow_mulVec_eq_smul`: an eigenvector of
  `A ^ F` in an `A`-stable subspace yields an eigenvector of `A` there, with eigenvalue an `F`-th
  root of the first.
-/

@[expose] public noncomputable section

open Matrix
open scoped Kronecker TensorProduct

namespace Stacks.EtaleCohomology

/-- **Eigenvalues of a power on a stable subspace.**  If `Z` is stable under the square matrix
`A` over an algebraically closed field, `ξ ∈ Z` is nonzero and `A ^ F ξ = c ξ` with `F > 0`, then
some nonzero `η ∈ Z` satisfies `A η = μ η` with `μ ^ F = c`. -/
public theorem exists_mulVec_eq_smul_pow_eq_of_pow_mulVec_eq_smul {K : Type*} [Field K]
    [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (Z : Submodule K (n → K)) (hZ : ∀ z ∈ Z, A *ᵥ z ∈ Z) {ξ : n → K} (hξZ : ξ ∈ Z) (hξ : ξ ≠ 0)
    {F : ℕ} (hF : 0 < F) {c : K} (h : (A ^ F) *ᵥ ξ = c • ξ) :
    ∃ η ∈ Z, η ≠ 0 ∧ ∃ μ : K, A *ᵥ η = μ • η ∧ μ ^ F = c := by
  let W : Submodule K (n → K) := Submodule.span K (Set.range fun k : Fin F => (A ^ (k : ℕ)) *ᵥ ξ)
  have hpowZ : ∀ k : ℕ, (A ^ k) *ᵥ ξ ∈ Z := fun k => by
    induction k with
    | zero => simpa using hξZ
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hZ _ ih
  have hWZ : W ≤ Z := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hpowZ k)
  -- `A` maps `W` into itself
  have hgen : ∀ k : ℕ, (A ^ k) *ᵥ ξ ∈ W := fun k => by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < F
      · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hk)
        rw [add_comm F j, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]
        exact W.smul_mem c (ih j (by omega))
  have hAW : ∀ w ∈ W, A *ᵥ w ∈ W := fun w hw => by
    refine (Submodule.span_le (p := W.comap (Matrix.toLin' A))).2 ?_ hw
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      ← pow_succ']
    exact hgen _
  -- `A ^ F` acts on `W` by `c`
  have hcW : ∀ w ∈ W, (A ^ F) *ᵥ w = c • w := fun w hw => by
    have := LinearMap.eqOn_span (f := Matrix.toLin' (A ^ F))
      (g := c • LinearMap.id) (s := Set.range fun k : Fin F => (A ^ (k : ℕ)) *ᵥ ξ) ?_ hw
    · simpa only [Matrix.toLin'_apply, LinearMap.smul_apply, LinearMap.id_apply] using this
    rintro _ ⟨k, rfl⟩
    simp only [Matrix.toLin'_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [Matrix.mulVec_mulVec, ← pow_add, add_comm, pow_add, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_smul]
  -- an eigenvector of `A` in `W`
  let f : Module.End K W := (Matrix.toLin' A).restrict (p := W) (q := W) fun w hw => by
    rw [Matrix.toLin'_apply]; exact hAW w hw
  have : Nontrivial W := ⟨⟨⟨ξ, Submodule.subset_span ⟨⟨0, hF⟩, by simp⟩⟩, 0, fun h0 =>
    hξ (congrArg Subtype.val h0)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨η, hη⟩ := hμ.exists_hasEigenvector
  have hfη : A *ᵥ (η : n → K) = μ • (η : n → K) := by
    have := congrArg Subtype.val hη.apply_eq_smul
    simpa [f, Matrix.toLin'_apply] using this
  have hpowη : ∀ k : ℕ, (A ^ k) *ᵥ (η : n → K) = μ ^ k • (η : n → K) := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hfη, smul_smul,
        ← pow_succ]
  have hη0 : (η : n → K) ≠ 0 := fun h0 => hη.2 (Subtype.ext h0)
  refine ⟨η, hWZ η.2, hη0, μ, hfη, ?_⟩
  have key : μ ^ F • (η : n → K) = c • (η : n → K) := by rw [← hpowη, hcW η η.2]
  by_contra hne
  exact hη0 (smul_right_injective _ (sub_ne_zero.2 hne) (by
    change (μ ^ F - c) • (η : n → K) = (μ ^ F - c) • 0
    rw [sub_smul, key, sub_self, smul_zero]))

/-! ### Kronecker products of vectors -/

section KroneckerVector

variable {K : Type*} [Field K]

/-- The Kronecker product `x ⊗ y` of two vectors, flattened along `finProdFinEquiv`. -/
public def kroneckerVec {a b : ℕ} (x : Fin a → K) (y : Fin b → K) : Fin (a * b) → K :=
  fun p => x (finProdFinEquiv.symm p).1 * y (finProdFinEquiv.symm p).2

/-- `tensorFinEquiv` sends a pure tensor `x ⊗ y` to the Kronecker product `kroneckerVec x y`. -/
theorem tensorFinEquiv_tmul {a b : ℕ} (x : Fin a → K) (y : Fin b → K) :
    tensorFinEquiv (x ⊗ₜ[K] y) = kroneckerVec x y := by
  funext p
  simp [tensorFinEquiv, kroneckerVec, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.equivFun_apply, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

/-- **`(A ⊗ B)(x ⊗ y) = A x ⊗ B y`** for flattened Kronecker products. -/
public theorem kroneckerMonoidHom_mulVec_kroneckerVec {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (x : Fin a → K) (y : Fin b → K) :
    kroneckerMonoidHom (A, B) *ᵥ kroneckerVec x y = kroneckerVec (A *ᵥ x) (B *ᵥ y) := by
  rw [← tensorFinEquiv_tmul, ← tensorFinEquiv_map, TensorProduct.map_tmul, Matrix.toLin'_apply,
    Matrix.toLin'_apply, tensorFinEquiv_tmul]

/-- The Kronecker product of nonzero vectors is nonzero. -/
public theorem kroneckerVec_ne_zero {a b : ℕ} {x : Fin a → K} {y : Fin b → K} (hx : x ≠ 0)
    (hy : y ≠ 0) : kroneckerVec x y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  intro h
  have := congrFun h (finProdFinEquiv (i, j))
  simp only [kroneckerVec, Equiv.symm_apply_apply, Pi.zero_apply] at this
  exact mul_ne_zero hi hj this

/-- The `n`-th Kronecker power `x ^ {⊗ n}` of a vector. -/
public def kroneckerPowVec {a : ℕ} (x : Fin a → K) : (n : ℕ) → Fin (a ^ n) → K
  | 0 => fun _ => 1
  | n + 1 => kroneckerVec (kroneckerPowVec x n) x

/-- A Kronecker power of a nonzero vector is nonzero. -/
public theorem kroneckerPowVec_ne_zero {a : ℕ} {x : Fin a → K} (hx : x ≠ 0) (n : ℕ) :
    kroneckerPowVec x n ≠ 0 := by
  induction n with
  | zero => exact Function.ne_iff.2 ⟨⟨0, by simp⟩, one_ne_zero⟩
  | succ n ih => exact kroneckerVec_ne_zero ih hx

/-- **`τ^{⊗ n}(g) x^{⊗ n} = (τ(g) x)^{⊗ n}`.** -/
public theorem tensorPowerRepresentation_mulVec_kroneckerPowVec {G : Type*} [Group G] {a : ℕ}
    (τ : G →* GL (Fin a) K) (g : G) (x : Fin a → K) (n : ℕ) :
    ((tensorPowerRepresentation τ n g : GL (Fin (a ^ n)) K) :
        Matrix (Fin (a ^ n)) (Fin (a ^ n)) K) *ᵥ kroneckerPowVec x n =
        kroneckerPowVec (((τ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ x) n := by
  induction n with
  | zero =>
    change (1 : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) K) *ᵥ _ = _
    rw [Matrix.one_mulVec]; rfl
  | succ n ih =>
    change kroneckerMonoidHom (((tensorPowerRepresentation τ n g : GL (Fin (a ^ n)) K) :
      Matrix (Fin (a ^ n)) (Fin (a ^ n)) K), ((τ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *ᵥ
        kroneckerVec (kroneckerPowVec x n) x = _
    rw [kroneckerMonoidHom_mulVec_kroneckerVec, ih]
    rfl

/-- `(c x) ⊗ (d y) = (c d) (x ⊗ y)` for flattened Kronecker products. -/
theorem kroneckerVec_smul {a b : ℕ} (x : Fin a → K) (y : Fin b → K) (c d : K) :
    kroneckerVec (c • x) (d • y) = (c * d) • kroneckerVec x y := by
  funext p
  simp only [kroneckerVec, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`x^{⊗ n}` scales by `c ^ n` when `x` scales by `c`.** -/
public theorem kroneckerPowVec_smul {a : ℕ} (x : Fin a → K) (c : K) (n : ℕ) :
    kroneckerPowVec (c • x) n = c ^ n • kroneckerPowVec x n := by
  induction n with
  | zero =>
    funext p
    change (1 : K) = (c ^ 0 • (fun _ : Fin (a ^ 0) => (1 : K))) p
    rw [Pi.smul_apply, pow_zero c, one_smul]
  | succ n ih =>
    change kroneckerVec (kroneckerPowVec (c • x) n) (c • x) =
      c ^ (n + 1) • kroneckerVec (kroneckerPowVec x n) x
    rw [ih, kroneckerVec_smul, pow_succ]

end KroneckerVector

/-! ### Permutation representations of finite quotients -/

section Permutation

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [DecidableEq X] {n : ℕ} (e : Fin n ≃ X)
  (R : Type*) [CommRing R]

/-- The permutation matrix of `g` acting on `X ≃ Fin n`: the `(i, j)` entry is `1` when
`e i = g • e j`. -/
public def permMatrix (g : G) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if e i = g • e j then 1 else 0

/-- `permMatrix e R` is multiplicative: the matrix of `g * h` is the product of the matrices. -/
theorem permMatrix_mul (g h : G) :
    permMatrix e R (g * h) = permMatrix e R g * permMatrix e R h := by
  classical
  ext i k
  simp only [permMatrix, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (e.symm (h • e k))]
  · simp [mul_smul]
  · intro j _ hj
    have : e j ≠ h • e k := fun h' => hj (by rw [← h', Equiv.symm_apply_apply])
    simp [this]
  · simp

/-- The permutation matrix of `1` is the identity matrix. -/
theorem permMatrix_one : permMatrix e R (1 : G) = 1 := by
  classical
  ext i j
  simp only [permMatrix, Matrix.of_apply, one_smul, Matrix.one_apply, e.apply_eq_iff_eq]

/-- **The permutation representation** of `G` on `X ≃ Fin n`. -/
@[sga "7 XVI 1.12" "more general"]
public def permMatrixRepresentation : G →* GL (Fin n) R where
  toFun g := ⟨permMatrix e R g, permMatrix e R g⁻¹, by rw [← permMatrix_mul, mul_inv_cancel,
    permMatrix_one], by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]⟩
  map_one' := Units.ext (permMatrix_one e R)
  map_mul' g h := Units.ext (permMatrix_mul e R g h)

/-- The underlying matrix of `permMatrixRepresentation e R g` is `permMatrix e R g`. -/
theorem permMatrixRepresentation_val (g : G) :
    ((permMatrixRepresentation e R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      permMatrix e R g :=
  rfl

/-- The permutation matrix applied to a vector permutes its coordinates. -/
theorem permMatrix_mulVec (g : G) (v : Fin n → R) (i : Fin n) :
    (permMatrix e R g *ᵥ v) i = v (e.symm (g⁻¹ • e i)) := by
  classical
  simp only [Matrix.mulVec, dotProduct, permMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm (g⁻¹ • e i))]
  · simp
  · intro j _ hj
    have : e i ≠ g • e j := fun h' => hj (by rw [h', inv_smul_smul, Equiv.symm_apply_apply])
    simp [this]
  · simp

end Permutation

end Stacks.EtaleCohomology

end
