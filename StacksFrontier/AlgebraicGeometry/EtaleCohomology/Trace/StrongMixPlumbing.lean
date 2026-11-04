module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyGroupTheory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.NilpotentMonodromyWeights
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Localization.Integer

/-!
# Fixed vectors along `ℤ_ℓ ⊆ ℚ_ℓ → ℂ`, Kronecker products and tensor products

Auxiliary linear algebra for the passage from Grothendieck's local monodromy theorem, which lives
over `ℤ_ℓ`, to the weight estimates of Weil II, Théorème 1.8.4, which are read in `ℂ` along an
embedding `ι : ℚ_ℓ → ℂ`:

* `Stacks.EtaleCohomology.exists_pow_mem_congruenceSubgroup`: some positive power of an element
  of `GL_r(ℤ_ℓ)` lies in `Γ(ℓ ^ n)` (the quotient `GL_r(ℤ / ℓ ^ n)` is finite);
* `Stacks.EtaleCohomology.mulVec_eq_self_of_forall_integral`: an inclusion of spaces of fixed
  vectors of two integral matrices, checked on integral vectors, holds over `ℚ_ℓ`;
* `Stacks.EtaleCohomology.mulVec_map_eq_zero_of_forall_mulVec_eq_zero`: an inclusion of kernels of
  two matrices over a field persists along any field embedding;
* `Stacks.EtaleCohomology.mulVec_map_eq_self_of_forall_integral`: the two combined, from `ℤ_ℓ` to
  `ℂ` along `ι`;
* `Stacks.EtaleCohomology.tensorFinEquiv_map`: under the coordinates `(Fin r → K) ⊗ (Fin s → K)
  ≃ (Fin (r * s) → K)`, the tensor product of the endomorphisms of two matrices is their
  flattened Kronecker product, and `Stacks.EtaleCohomology.dualTensorFinEquiv_map` the same for
  the transposes of the endomorphisms on the duals.
-/

@[expose] public noncomputable section

open Matrix
open scoped Kronecker TensorProduct

namespace Stacks.EtaleCohomology

section Congruence

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- **Some positive power of an element of `GL_r(ℤ_ℓ)` lies in `Γ(ℓ ^ n)`**: the reductions of
its powers modulo `ℓ ^ n` repeat. -/
public theorem exists_pow_mem_congruenceSubgroup (g : GL (Fin r) ℤ_[ℓ]) (n : ℕ) :
    ∃ f : ℕ, 0 < f ∧ g ^ f ∈ congruenceSubgroup ℓ r n := by
  let red : ℕ → Matrix (Fin r) (Fin r) (ZMod (ℓ ^ n)) := fun k =>
    ((g ^ k : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (PadicInt.toZModPow n)
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite red
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
  refine ⟨b - a, Nat.sub_pos_of_lt hlt, fun i j => ?_⟩
  have hdiff : ∀ i j, (ℓ : ℤ_[ℓ]) ^ n ∣
      (((g ^ b : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) -
        ((g ^ a : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ])) i j := fun i j => by
    have h := congrFun (congrFun he i) j
    simp only [red, Matrix.map_apply] at h
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply,
      map_sub, h, sub_self]
  have hrw : ((g ^ (b - a) : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1 =
      (((g ^ a)⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *
        (((g ^ b : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) -
          ((g ^ a : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ])) := by
    have hu : (g ^ a)⁻¹ * g ^ b = g ^ (b - a) := by
      rw [← pow_mul_pow_sub g hlt.le, inv_mul_cancel_left]
    rw [mul_sub, ← Units.val_mul, ← Units.val_mul, hu, inv_mul_cancel, Units.val_one]
  rw [hrw]
  exact dvd_mul_apply_of_dvd_right hdiff i j

end Congruence

section FixedVectors

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Fixed vectors over `ℚ_ℓ` from integral ones.**  If every integral vector fixed by `M` is
fixed by `M'`, then every vector of `ℚ_ℓ ^ n` fixed by `M` is fixed by `M'`: clear denominators. -/
public theorem mulVec_eq_self_of_forall_integral {M M' : Matrix n n ℤ_[ℓ]}
    (h : ∀ v : n → ℤ_[ℓ], M *ᵥ v = v → M' *ᵥ v = v) (w : n → ℚ_[ℓ])
    (hw : M.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ w = w) :
    M'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ w = w := by
  obtain ⟨⟨c, hc⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[ℓ]) w
  choose u hu using hint
  have hcw : algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ u = c • w := funext fun i => by
    simp only [Function.comp_apply, hu i, Pi.smul_apply]
  have hinj : Function.Injective (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := IsFractionRing.injective _ _
  have hMu : M *ᵥ u = u := funext fun i => hinj (by
    rw [RingHom.map_mulVec, hcw, Matrix.mulVec_smul, hw, ← hcw]; rfl)
  have hM'u := h u hMu
  have hc0 : (algebraMap ℤ_[ℓ] ℚ_[ℓ] c) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hc)
  have key : c • (M'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ w) = c • w := by
    rw [← Matrix.mulVec_smul, ← hcw]
    funext i
    rw [← RingHom.map_mulVec, hM'u]; rfl
  funext i
  have := congrFun key i
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  exact mul_left_cancel₀ hc0 this

/-- **Inclusions of kernels persist along field embeddings.**  If every vector killed by `A` is
killed by `B`, for matrices over a field `K`, then the same holds for their images under any ring
homomorphism `ι : K → L` to a field: `B` factors as `C * A`. -/
public theorem mulVec_map_eq_zero_of_forall_mulVec_eq_zero {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) {A B : Matrix n n K} (h : ∀ v : n → K, A *ᵥ v = 0 → B *ᵥ v = 0)
    (w : n → L) (hw : A.map ι *ᵥ w = 0) : B.map ι *ᵥ w = 0 := by
  -- each row of `B` is a linear form vanishing on `ker A`, hence factors through `A`
  have hrow : ∀ i : n, ∃ ψ : (n → K) →ₗ[K] K, ∀ y, ψ (A *ᵥ y) = (B *ᵥ y) i := by
    intro i
    refine exists_comp_eq_of_ker_le (g := Matrix.mulVecLin A)
      (f := (LinearMap.proj i).comp (Matrix.mulVecLin B)) fun y hy => ?_
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    simp [h y hy]
  choose ψ hψ using hrow
  let C : Matrix n n K := LinearMap.toMatrix' (LinearMap.pi ψ)
  have hBC : B = C * A := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    funext i
    rw [LinearMap.pi_apply, hψ i y]
  rw [hBC, Matrix.map_mul, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]

/-- **Fixed vectors over `ℂ` from integral ones.**  If every integral vector fixed by `M` is
fixed by `M'`, then the same holds over any field receiving `ℚ_ℓ`, for the images of `M` and
`M'`. -/
public theorem mulVec_map_eq_self_of_forall_integral {L : Type*} [Field L] (ι : ℚ_[ℓ] →+* L)
    {M M' : Matrix n n ℤ_[ℓ]} (h : ∀ v : n → ℤ_[ℓ], M *ᵥ v = v → M' *ᵥ v = v) (w : n → L)
    (hw : M.map (ι.comp (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ w = w) :
    M'.map (ι.comp (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ w = w := by
  have hQ : ∀ v : n → ℚ_[ℓ], (M.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) - 1) *ᵥ v = 0 →
      (M'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) - 1) *ᵥ v = 0 := fun v hv => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv ⊢
    exact mulVec_eq_self_of_forall_integral h v hv
  have key : ∀ N : Matrix n n ℤ_[ℓ], (N.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) - 1).map ι *ᵥ w = 0 ↔
      N.map (ι.comp (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ w = w := fun N => by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_zero, Matrix.map_map]
    rfl
  exact (key M').1 (mulVec_map_eq_zero_of_forall_mulVec_eq_zero ι hQ w ((key M).2 hw))

end FixedVectors

section Tensor

variable {K : Type*} [Field K] {r s : ℕ}

/-- The coordinates `(Fin r → K) ⊗ (Fin s → K) ≃ (Fin (r * s) → K)` of the tensor product basis,
flattened along `finProdFinEquiv`. -/
public def tensorFinEquiv : (Fin r → K) ⊗[K] (Fin s → K) ≃ₗ[K] (Fin (r * s) → K) :=
  ((Pi.basisFun K (Fin r)).tensorProduct (Pi.basisFun K (Fin s))).equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft K K finProdFinEquiv.symm

/-- The coordinates `(K^r)^∨ ⊗ (K^s)^∨ ≃ (Fin (r * s) → K)` of the tensor product of the dual
bases, flattened along `finProdFinEquiv`. -/
public def dualTensorFinEquiv :
    Module.Dual K (Fin r → K) ⊗[K] Module.Dual K (Fin s → K) ≃ₗ[K] (Fin (r * s) → K) :=
  ((Pi.basisFun K (Fin r)).dualBasis.tensorProduct (Pi.basisFun K (Fin s)).dualBasis).equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft K K finProdFinEquiv.symm

/-- Reindexing a matrix on `Fin r × Fin s` along `finProdFinEquiv` commutes with `mulVec`: the
reindexed matrix applied to the flattened vector is the flattening of `M *ᵥ v`. -/
theorem reindex_finProdFinEquiv_mulVec (M : Matrix (Fin r × Fin s) (Fin r × Fin s) K)
    (v : Fin r × Fin s → K) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv M *ᵥ (v ∘ finProdFinEquiv.symm) =
      (M *ᵥ v) ∘ finProdFinEquiv.symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id]

/-- Precomposition with `finProdFinEquiv.symm` is the coordinate flattening `v ∘ symm`. -/
private theorem funLeft_finProdFinEquiv_symm (v : Fin r × Fin s → K) :
    LinearMap.funLeft K K finProdFinEquiv.symm v = v ∘ finProdFinEquiv.symm :=
  funext fun _ => LinearMap.funLeft_apply _ _ _ _ _

/-- **Tensor products of matrix endomorphisms are Kronecker products in coordinates.** -/
public theorem tensorFinEquiv_map (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin s) (Fin s) K)
    (X : (Fin r → K) ⊗[K] (Fin s → K)) :
    tensorFinEquiv (TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' B) X) =
      kroneckerMonoidHom (A, B) *ᵥ tensorFinEquiv X := by
  simp only [tensorFinEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    kroneckerMonoidHom_apply]
  rw [funLeft_finProdFinEquiv_symm, funLeft_finProdFinEquiv_symm, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr
      ((Pi.basisFun K (Fin r)).tensorProduct (Pi.basisFun K (Fin s)))
      ((Pi.basisFun K (Fin r)).tensorProduct (Pi.basisFun K (Fin s))),
    TensorProduct.toMatrix_map, LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin']
  exact (reindex_finProdFinEquiv_mulVec _ _).symm

/-- **Tensor products of transposes of matrix endomorphisms on duals are Kronecker products of the
transposed matrices in coordinates.** -/
public theorem dualTensorFinEquiv_map (A : Matrix (Fin r) (Fin r) K)
    (B : Matrix (Fin s) (Fin s) K)
    (X : Module.Dual K (Fin r → K) ⊗[K] Module.Dual K (Fin s → K)) :
    dualTensorFinEquiv (TensorProduct.map (Matrix.toLin' A).dualMap (Matrix.toLin' B).dualMap X) =
      kroneckerMonoidHom (Aᵀ, Bᵀ) *ᵥ dualTensorFinEquiv X := by
  simp only [dualTensorFinEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    kroneckerMonoidHom_apply]
  rw [funLeft_finProdFinEquiv_symm, funLeft_finProdFinEquiv_symm, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr
      ((Pi.basisFun K (Fin r)).dualBasis.tensorProduct (Pi.basisFun K (Fin s)).dualBasis)
      ((Pi.basisFun K (Fin r)).dualBasis.tensorProduct (Pi.basisFun K (Fin s)).dualBasis),
    TensorProduct.toMatrix_map, LinearMap.dualMap_def,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, LinearMap.toMatrix_transpose,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_toLin']
  exact (reindex_finProdFinEquiv_mulVec _ _).symm

end Tensor

end Stacks.EtaleCohomology

end
