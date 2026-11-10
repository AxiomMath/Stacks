module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# Base change of an inverse limit along a finite free module

Let `A` be a commutative ring, `(Mₙ, t n : M (n + 1) → Mₙ)` an inverse system of `A`-modules with
limit `lim_n Mₙ = ` `invLimit M t`, and `N` an `A`-module.  Base change along `N` turns the system
into the system `(N ⊗_A Mₙ)` with transition maps `N ⊗ t n`, and there is a canonical comparison
map

`N ⊗_A (lim_n Mₙ) ⟶ lim_n (N ⊗_A Mₙ)`,

namely the one assembled from the base changes `N ⊗ pr_n` of the limit projections.  This file
constructs that map and proves that **it is bijective when `N` is free of finite rank**.

Neither finiteness nor freeness can be dropped.  For `N` free on an infinite basis `κ` the left
side is the finitely supported families `κ →₀ lim_n Mₙ` and the right side contains families whose
support grows with `n`, so the map is not surjective; and for `N` merely flat the statement is
false already for towers of finite length.  The proof is the only argument available at this
generality: a finite basis of `N` turns both sides into `κ`-indexed tuples — on the left because
`N ⊗_A P ≅ κ → P` naturally in `P`, on the right because a product indexed by a *finite* set
commutes with the limit — and the comparison map becomes the identity of `κ → lim_n Mₙ`.

## Main definitions

* `tensorCoord` — the `i`-th coordinate `N ⊗_A P ⟶ P` of a base change along a module with a
  chosen basis, and `tensorOfCoord` its inverse, assembling `∑ i, b i ⊗ f i`.
* `tensorCoordEquiv` — the resulting `N ⊗_A P ≃ₗ[A] (κ → P)` for a finite basis `b` of `N`.
* `invLimitTensor` — the limit `lim_n (N ⊗_A Mₙ)` of the base-changed system.
* `invLimitTensorMap` — **the comparison map** `N ⊗_A (lim_n Mₙ) ⟶ lim_n (N ⊗_A Mₙ)`.
* `invLimitTensorEquiv` — the comparison map as a linear equivalence, for `N` finite free.

## Main results

* `tensorCoord_lTensor` — the coordinates of a base change are natural in the module.
* `bijective_invLimitTensorMap` — **base change along a finite free module commutes with the
  limit of an inverse system of modules.**
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

/-! ### Coordinates of a base change along a module with a chosen basis -/

section FreeCoordinates

variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N] {κ : Type*}
  (b : Module.Basis κ A N) (P : Type w) [AddCommGroup P] [Module A P]

/-- **The `i`-th coordinate of a base change along a module with a chosen basis**: the map
`N ⊗_A P ⟶ P` induced by the `i`-th coordinate function `b.coord i : N ⟶ A`, which sends
`n ⊗ x` to `(b.repr n i) · x`.  Written through these coordinates the base change becomes
a `κ`-indexed tuple of elements of `P`. -/
def tensorCoord (i : κ) : N ⊗[A] P →ₗ[A] P :=
  (TensorProduct.lid A P).toLinearMap ∘ₗ TensorProduct.map (b.coord i) LinearMap.id

/-- The `i`-th coordinate of `n ⊗ x` is `(b.repr n i) • x`. -/
@[simp] theorem tensorCoord_tmul (i : κ) (n : N) (x : P) :
    tensorCoord b P i (n ⊗ₜ[A] x) = b.repr n i • x := by
  simp [tensorCoord]

/-- **The coordinates of a base change are natural in the module**: for `φ : P ⟶ Q`, the `i`-th
coordinate of `(N ⊗ φ) z` is `φ` applied to the `i`-th coordinate of `z`. -/
theorem tensorCoord_lTensor {Q : Type w} [AddCommGroup Q] [Module A Q] (phi : P →ₗ[A] Q) (i : κ)
    (z : N ⊗[A] P) :
    tensorCoord b Q i (LinearMap.lTensor N phi z) = phi (tensorCoord b P i z) := by
  induction z using TensorProduct.inductionOn with
  | tmul n x => rw [LinearMap.lTensor_tmul, tensorCoord_tmul, tensorCoord_tmul, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

variable [Fintype κ]

/-- **A base change along a module with a chosen finite basis, assembled from its coordinates**:
the tuple `f` goes to `∑ i, b i ⊗ f i`. -/
def tensorOfCoord : (κ → P) →ₗ[A] N ⊗[A] P where
  toFun f := ∑ i, b i ⊗ₜ[A] f i
  map_add' f h := by
    simp only [Pi.add_apply, TensorProduct.tmul_add]
    exact Finset.sum_add_distrib
  map_smul' c f := by
    simp only [Pi.smul_apply, TensorProduct.tmul_smul, Finset.smul_sum]
    rfl

/-- `tensorOfCoord b P f` is `∑ i, b i ⊗ f i`. -/
@[simp] theorem tensorOfCoord_apply (f : κ → P) :
    tensorOfCoord b P f = ∑ i, b i ⊗ₜ[A] f i :=
  rfl

/-- The `i`-th coordinate of `∑ j, b j ⊗ f j` is `f i`. -/
@[simp] theorem tensorCoord_tensorOfCoord (i : κ) (f : κ → P) :
    tensorCoord b P i (tensorOfCoord b P f) = f i := by
  classical
  rw [tensorOfCoord_apply, map_sum, Finset.sum_eq_single i]
  · rw [tensorCoord_tmul, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  · intro j _ hj
    rw [tensorCoord_tmul, Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hj, zero_smul]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- An element `z` of `N ⊗_A P` is the sum `∑ i, b i ⊗ zᵢ` of its coordinates `zᵢ`. -/
@[simp] theorem tensorOfCoord_tensorCoord (z : N ⊗[A] P) :
    tensorOfCoord b P (fun i ↦ tensorCoord b P i z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul n x =>
    simp only [tensorCoord_tmul, tensorOfCoord_apply]
    rw [Finset.sum_congr rfl fun i _ ↦ (TensorProduct.smul_tmul (b.repr n i) (b i) x).symm,
      ← TensorProduct.sum_tmul, b.sum_repr n]
  | add z w hz hw =>
    rw [show (fun i ↦ tensorCoord b P i (z + w)) =
        (fun i ↦ tensorCoord b P i z) + (fun i ↦ tensorCoord b P i w) from
      funext fun i ↦ map_add _ _ _, map_add, hz, hw]

/-- **A base change along a module with a chosen finite basis is the tuple of its coordinates**:
the linear equivalence `N ⊗_A P ≃ (κ → P)` sending `z` to `fun i ↦ tensorCoord b P i z`. -/
def tensorCoordEquiv : N ⊗[A] P ≃ₗ[A] (κ → P) where
  toFun z := fun i ↦ tensorCoord b P i z
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ map_smul _ _ _
  invFun := tensorOfCoord b P
  left_inv := tensorOfCoord_tensorCoord b P
  right_inv f := funext fun i ↦ tensorCoord_tensorOfCoord b P i f

/-- The `i`-th component of `tensorCoordEquiv b P z` is the `i`-th coordinate of `z`. -/
@[simp] theorem tensorCoordEquiv_apply (z : N ⊗[A] P) (i : κ) :
    tensorCoordEquiv b P z i = tensorCoord b P i z :=
  rfl

end FreeCoordinates

/-! ### The base change of an inverse system, and the comparison map -/

section InvLimitTensor

variable {A : Type u} [CommRing A] (N : Type v) [AddCommGroup N] [Module A N] (M : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)] (t : ∀ n, M (n + 1) →ₗ[A] M n)

/-- The limit projections of an inverse system are compatible with the transition maps, as an
equation of linear maps: `t n ∘ pr_{n+1} = pr_n`. -/
theorem invLimit.proj_comp_eq (n : ℕ) :
    (t n).comp (invLimit.proj M t (n + 1)) = invLimit.proj M t n :=
  LinearMap.ext fun x ↦ invLimit.proj_comp_transition M t n x

/-- **The limit of the base change of an inverse system along `N`**: the system `(N ⊗_A Mₙ)` with
transition maps `N ⊗ t n`, and its limit. -/
def invLimitTensor : Submodule A (∀ n, N ⊗[A] M n) :=
  invLimit (fun n ↦ N ⊗[A] M n) fun n ↦ LinearMap.lTensor N (t n)

/-- A family `x n ∈ N ⊗_A Mₙ` lies in `invLimitTensor N M t` if and only if
`(N ⊗ t n) (x (n + 1)) = x n` for every `n`. -/
theorem mem_invLimitTensor_iff (x : ∀ n, N ⊗[A] M n) :
    x ∈ invLimitTensor N M t ↔ ∀ n, LinearMap.lTensor N (t n) (x (n + 1)) = x n :=
  Iff.rfl

/-- **The comparison map `N ⊗_A (lim_n Mₙ) ⟶ lim_n (N ⊗_A Mₙ)`**, assembled from the base changes
`N ⊗ pr_n` of the limit projections. -/
def invLimitTensorMap :
    N ⊗[A] ↥(invLimit M t) →ₗ[A] ↥(invLimitTensor N M t) :=
  LinearMap.codRestrict _ (LinearMap.pi fun n ↦ LinearMap.lTensor N (invLimit.proj M t n))
    fun z n ↦ by
      change LinearMap.lTensor N (t n)
          ((LinearMap.pi fun k ↦ LinearMap.lTensor N (invLimit.proj M t k)) z (n + 1)) =
        (LinearMap.pi fun k ↦ LinearMap.lTensor N (invLimit.proj M t k)) z n
      simp only [LinearMap.pi_apply]
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, invLimit.proj_comp_eq]

/-- The `n`-th component of `invLimitTensorMap N M t z` is `(N ⊗ pr_n) z`. -/
@[simp] theorem invLimitTensorMap_val (z : N ⊗[A] ↥(invLimit M t)) (n : ℕ) :
    (invLimitTensorMap N M t z).val n = LinearMap.lTensor N (invLimit.proj M t n) z :=
  rfl

variable {κ : Type*} [Finite κ]

/-- **Base change along a module free of finite rank commutes with the limit of an inverse system
of modules**: the comparison map `N ⊗_A (lim_n Mₙ) ⟶ lim_n (N ⊗_A Mₙ)` is bijective. -/
theorem bijective_invLimitTensorMap (b : Module.Basis κ A N) :
    Function.Bijective (invLimitTensorMap N M t) := by
  have := Fintype.ofFinite κ
  constructor
  · intro z w hzw
    have hlev : ∀ n : ℕ, LinearMap.lTensor N (invLimit.proj M t n) z =
        LinearMap.lTensor N (invLimit.proj M t n) w := fun n ↦ congrArg (fun x ↦ x.val n) hzw
    have hcoord : ∀ i : κ, tensorCoord b ↥(invLimit M t) i z = tensorCoord b ↥(invLimit M t) i w :=
      fun i ↦ Subtype.ext (funext fun n ↦ by
        have hz := tensorCoord_lTensor b ↥(invLimit M t) (invLimit.proj M t n) i z
        have hw := tensorCoord_lTensor b ↥(invLimit M t) (invLimit.proj M t n) i w
        rw [hlev n, hw] at hz
        exact hz.symm)
    rw [← tensorOfCoord_tensorCoord b ↥(invLimit M t) z,
      ← tensorOfCoord_tensorCoord b ↥(invLimit M t) w, funext hcoord]
  · intro y
    refine ⟨tensorOfCoord b ↥(invLimit M t) fun i ↦
      ⟨fun n ↦ tensorCoord b (M n) i (y.val n), fun n ↦ ?_⟩, Subtype.ext (funext fun n ↦ ?_)⟩
    · rw [← tensorCoord_lTensor b (M (n + 1)) (t n) i (y.val (n + 1)), y.property n]
    · rw [invLimitTensorMap_val, tensorOfCoord_apply, map_sum]
      refine (Finset.sum_congr rfl fun i _ ↦ LinearMap.lTensor_tmul N _ (b i) _).trans ?_
      exact (tensorOfCoord_apply b (M n) fun i ↦ tensorCoord b (M n) i (y.val n)).symm.trans
        (tensorOfCoord_tensorCoord b (M n) (y.val n))

/-- **The comparison map of `invLimitTensorMap` as a linear equivalence**, for `N` free of finite
rank: `N ⊗_A (lim_n Mₙ) ≅ lim_n (N ⊗_A Mₙ)`. -/
def invLimitTensorEquiv (b : Module.Basis κ A N) :
    N ⊗[A] ↥(invLimit M t) ≃ₗ[A] ↥(invLimitTensor N M t) :=
  LinearEquiv.ofBijective (invLimitTensorMap N M t) (bijective_invLimitTensorMap N M t b)

/-- The `n`-th component of `invLimitTensorEquiv N M t b z` is `(N ⊗ pr_n) z`. -/
@[simp] theorem invLimitTensorEquiv_apply_val (b : Module.Basis κ A N)
    (z : N ⊗[A] ↥(invLimit M t)) (n : ℕ) :
    (invLimitTensorEquiv N M t b z).val n = LinearMap.lTensor N (invLimit.proj M t n) z :=
  rfl

end InvLimitTensor

end

end
