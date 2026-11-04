module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula

/-!
# The exterior power as a quotient of the tensor power, in coordinates

For `V = Rʳ` the `k`-th Kronecker power `A^{⊗ k}` of a matrix, flattened to `Fin (r ^ k)` as in
`Stacks.EtaleCohomology.tensorPowerRepresentation`, has entries
`A^{⊗ k}_{I J} = ∏_t A_{I_t J_t}` where `I ↦ (I_0, …, I_{k-1})` identifies `Fin (r ^ k)` with
`k`-tuples.  The linear map `V^{⊗ k} → ⋀ᵏ V`,
`e_{I_0} ⊗ ⋯ ⊗ e_{I_{k-1}} ↦ e_{I_0} ∧ ⋯ ∧ e_{I_{k-1}}`, has a matrix `P` with integer entries,
a right inverse `Q` (the sorted tuples), and intertwines `A^{⊗ k}` with the compound matrix
`⋀ᵏ A`: `P A^{⊗ k} = (⋀ᵏ A) P`.  Hence `⋀ᵏ A = P A^{⊗ k} Q`, and
`A^{⊗ k}` preserves the kernel of `P`: the exterior power is a compression of the tensor power,
which is how determinantal weights pass to exterior powers (Weil II 1.3.13; Kedlaya, *Fourier
transforms and p-adic Weil II*, Proposition 6.1.6 (iii)).

## Main definitions

* `Stacks.EtaleCohomology.tensorIndexEquiv`: `Fin (r ^ k) ≃ (Fin k → Fin r)`.
* `Stacks.EtaleCohomology.kronPowMatrix`: `A ↦ A^{⊗ k}`.
* `Stacks.EtaleCohomology.exteriorProjection`, `Stacks.EtaleCohomology.exteriorSection`: `P`, `Q`.

## Main results

* `Stacks.EtaleCohomology.kronPowMatrix_apply`: the entries of `A^{⊗ k}`.
* `Stacks.EtaleCohomology.tensorPowerRepresentation_val`: `τ^{⊗ k}(g)` is the Kronecker power
  of `τ(g)`.
* `Stacks.EtaleCohomology.exteriorProjection_mul_kronPowMatrix`: `P A^{⊗ k} = (⋀ᵏ A) P`.
* `Stacks.EtaleCohomology.exteriorProjection_mul_exteriorSection`: `P Q = 1`.
* `Stacks.EtaleCohomology.exteriorProjection_apply`: the entries of `P` are integers.
-/

@[expose] public noncomputable section

open Matrix Set.powersetCard
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {R : Type*} [CommRing R]

/-- The identification of the flattened Kronecker index set `Fin (r ^ k)` with `k`-tuples, the
last factor being the last coordinate. -/
public def tensorIndexEquiv (r : ℕ) : (k : ℕ) → Fin (r ^ k) ≃ (Fin k → Fin r)
  | 0 => (finCongr (pow_zero r)).trans (Equiv.ofUnique (Fin 1) (Fin 0 → Fin r))
  | k + 1 => finProdFinEquiv.symm.trans
      (((tensorIndexEquiv r k).prodCongr (Equiv.refl (Fin r))).trans
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => Fin r)))

public theorem tensorIndexEquiv_succ_apply {r k : ℕ} (a : Fin (r ^ k)) (i : Fin r) :
    tensorIndexEquiv r (k + 1) (finProdFinEquiv (a, i)) = Fin.snoc (tensorIndexEquiv r k a) i := by
  show (finProdFinEquiv.symm.trans (((tensorIndexEquiv r k).prodCongr (Equiv.refl (Fin r))).trans
      ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => Fin r)))) (finProdFinEquiv (a, i)) = _
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- **The `k`-th Kronecker power** `A^{⊗ k}` of a square matrix, flattened to `Fin (r ^ k)`. -/
public def kronPowMatrix {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    (k : ℕ) → Matrix (Fin (r ^ k)) (Fin (r ^ k)) R
  | 0 => 1
  | k + 1 => Matrix.reindex finProdFinEquiv finProdFinEquiv (kronPowMatrix A k ⊗ₖ A)

/-- **The entries of `A^{⊗ k}`**: `A^{⊗ k}_{I J} = ∏_t A_{I_t J_t}`. -/
public theorem kronPowMatrix_apply {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (k : ℕ)
    (I J : Fin (r ^ k)) :
    kronPowMatrix A k I J = ∏ t, A (tensorIndexEquiv r k I t) (tensorIndexEquiv r k J t) := by
  induction k with
  | zero =>
    have hIJ : I = J := Fin.ext (by have := I.2; have := J.2; simp only [pow_zero] at *; omega)
    subst hIJ
    simp [kronPowMatrix]
  | succ k ih =>
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective I
    obtain ⟨⟨b, l⟩, rfl⟩ := finProdFinEquiv.surjective J
    rw [Fin.prod_univ_castSucc]
    simp only [tensorIndexEquiv_succ_apply, Fin.snoc_castSucc, Fin.snoc_last, ← ih]
    simp [kronPowMatrix]

/-- `τ^{⊗ k}(g)` is the Kronecker power of `τ(g)`. -/
public theorem tensorPowerRepresentation_val {Γ : Type*} [Group Γ] {r : ℕ} (τ : Γ →* GL (Fin r) R)
    (k : ℕ) (g : Γ) :
    (tensorPowerRepresentation τ k g : Matrix (Fin (r ^ k)) (Fin (r ^ k)) R) =
      kronPowMatrix (τ g : Matrix (Fin r) (Fin r) R) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (kroneckerRepresentation (tensorPowerRepresentation τ k) τ g).val = _
    rw [kroneckerRepresentation_val, ih]
    rfl

variable (R) (r k : ℕ)

/-- The linear map `V^{⊗ k} → ⋀ᵏ V`, `e_I ↦ e_{I_0} ∧ ⋯ ∧ e_{I_{k-1}}`, for `V = Rʳ`. -/
public def exteriorTensorMap : (Fin (r ^ k) → R) →ₗ[R] ⋀[R]^k (Fin r → R) :=
  (Pi.basisFun R (Fin (r ^ k))).constr R fun I =>
    exteriorPower.ιMulti R k fun t => Pi.single (tensorIndexEquiv r k I t) (1 : R)

/-- **The matrix `P` of `V^{⊗ k} → ⋀ᵏ V`** in the standard bases. -/
public def exteriorProjection : Matrix (Set.powersetCard (Fin r) k) (Fin (r ^ k)) R :=
  LinearMap.toMatrix (Pi.basisFun R (Fin (r ^ k))) ((Pi.basisFun R (Fin r)).exteriorPower k)
    (exteriorTensorMap R r k)

/-- **The right inverse `Q`**: `e_S ↦ e_{s_0} ⊗ ⋯ ⊗ e_{s_{k-1}}` for the increasing enumeration of
`S`. -/
public def exteriorSection : Matrix (Fin (r ^ k)) (Set.powersetCard (Fin r) k) R :=
  fun I S => if I = (tensorIndexEquiv r k).symm (ofFinEmbEquiv.symm S) then 1 else 0

variable {R r k}

/-- `exteriorTensorMap` sends the basis vector `e_I` to `e_{I_0} ∧ ⋯ ∧ e_{I_{k-1}}`. -/
theorem exteriorTensorMap_single (I : Fin (r ^ k)) :
    exteriorTensorMap R r k (Pi.single I 1) =
      exteriorPower.ιMulti R k fun t => Pi.single (tensorIndexEquiv r k I t) (1 : R) := by
  rw [exteriorTensorMap, ← Pi.basisFun_apply, Module.Basis.constr_basis]

/-- **`⋀ᵏ` is a quotient of `⊗ᵏ`, equivariantly**: `P ∘ A^{⊗ k} = ⋀ᵏ A ∘ P`. -/
public theorem exteriorTensorMap_comp (A : Matrix (Fin r) (Fin r) R) :
    exteriorTensorMap R r k ∘ₗ Matrix.toLin' (kronPowMatrix A k) =
      exteriorPower.map k (Matrix.toLin' A) ∘ₗ exteriorTensorMap R r k := by
  refine (Pi.basisFun R (Fin (r ^ k))).ext fun I => ?_
  rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply, exteriorTensorMap_single,
    exteriorPower.map_apply_ιMulti, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  -- the left side
  have hL : exteriorTensorMap R r k ((kronPowMatrix A k).col I) =
      ∑ J, kronPowMatrix A k J I •
        exteriorPower.ιMulti R k fun t => Pi.single (tensorIndexEquiv r k J t) (1 : R) := by
    rw [exteriorTensorMap, Module.Basis.constr_apply_fintype]
    rfl
  rw [hL]
  -- the right side: expand by multilinearity
  have hcol : ∀ t, Matrix.toLin' A (Pi.single (tensorIndexEquiv r k I t) (1 : R)) =
      ∑ a, A a (tensorIndexEquiv r k I t) • Pi.single a (1 : R) := by
    intro t
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    ext b
    simp [Finset.sum_apply, Pi.single_apply]
  have hfun : (⇑(Matrix.toLin' A) ∘ fun t => Pi.single (tensorIndexEquiv r k I t) (1 : R)) =
      fun t => ∑ a, A a (tensorIndexEquiv r k I t) • Pi.single a (1 : R) := funext hcol
  rw [hfun]
  have hR := (exteriorPower.ιMulti R k).toMultilinearMap.map_sum
    (fun t a => A a (tensorIndexEquiv r k I t) • Pi.single a (1 : R))
  rw [AlternatingMap.coe_multilinearMap] at hR
  rw [hR]
  refine (Fintype.sum_equiv (tensorIndexEquiv r k) _ _ fun J => ?_)
  have hs := (exteriorPower.ιMulti R k).toMultilinearMap.map_smul_univ
    (fun t => A (tensorIndexEquiv r k J t) (tensorIndexEquiv r k I t))
    (fun t => (Pi.single (tensorIndexEquiv r k J t) (1 : R) : Fin r → R))
  rw [AlternatingMap.coe_multilinearMap] at hs
  rw [hs, kronPowMatrix_apply]

/-- **`P A^{⊗ k} = (⋀ᵏ A) P`.** -/
public theorem exteriorProjection_mul_kronPowMatrix (A : Matrix (Fin r) (Fin r) R) :
    exteriorProjection R r k * kronPowMatrix A k =
      compoundMonoidHom k A * exteriorProjection R r k := by
  have h := congrArg (LinearMap.toMatrix (Pi.basisFun R (Fin (r ^ k)))
    ((Pi.basisFun R (Fin r)).exteriorPower k)) (exteriorTensorMap_comp (k := k) A)
  rw [LinearMap.toMatrix_comp _ (Pi.basisFun R (Fin (r ^ k))), LinearMap.toMatrix_comp _
    ((Pi.basisFun R (Fin r)).exteriorPower k), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at h
  exact h

/-- **`P Q = 1`.** -/
public theorem exteriorProjection_mul_exteriorSection :
    exteriorProjection R r k * exteriorSection R r k = 1 := by
  ext S' S
  rw [Matrix.mul_apply]
  simp only [exteriorSection, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [exteriorProjection, LinearMap.toMatrix_apply, Pi.basisFun_apply, exteriorTensorMap_single]
  have hb : (exteriorPower.ιMulti R k fun t => Pi.single (tensorIndexEquiv r k
      ((tensorIndexEquiv r k).symm (ofFinEmbEquiv.symm S)) t) (1 : R)) =
      (Pi.basisFun R (Fin r)).exteriorPower k S := by
    rw [Equiv.apply_symm_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    funext t
    simp [Pi.basisFun_apply]
  rw [hb, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- **The entries of `P` are integers**: determinants of `0`-`1` matrices. -/
public theorem exteriorProjection_apply (S : Set.powersetCard (Fin r) k) (I : Fin (r ^ k)) :
    exteriorProjection R r k S I =
      (((Matrix.of fun i j => if tensorIndexEquiv r k I i = ofFinEmbEquiv.symm S j then (1 : ℤ)
        else 0).det : ℤ) : R) := by
  rw [exteriorProjection, LinearMap.toMatrix_apply, Pi.basisFun_apply, exteriorTensorMap_single,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  rw [show ((Matrix.of fun i j => if tensorIndexEquiv r k I i = ofFinEmbEquiv.symm S j then (1 : ℤ)
      else 0).det : R) = Int.castRingHom R (Matrix.of fun i j =>
        if tensorIndexEquiv r k I i = ofFinEmbEquiv.symm S j then (1 : ℤ) else 0).det from rfl,
    RingHom.map_det]
  congr 1
  ext i j
  simp [Pi.single_apply, eq_comm]

end Stacks.EtaleCohomology

end
