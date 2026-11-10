module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Moving the left factor of a tensor product across a base change of its ring

Let `φ : R ⟶ R'` be a homomorphism of commutative rings, let `N` be an `R`-module with a basis
`b`, let `N'` be an `R'`-module and let `u : N ⟶ N'` be an additive map which is semilinear for
`φ`.  Suppose that the images `u (b i)` of the basis form a basis of `N'` over `R'`; that is the
statement that `u` presents `N'` as the base change `R' ⊗_R N`, written through the bases rather
than through a tensor product.

Then for **every** `R'`-module `M`, read as an `R`-module through `φ`, the map

`N ⊗_R M ⟶ N' ⊗_{R'} M`,  `n ⊗ m ↦ u n ⊗ m`,

is an isomorphism of additive groups: `Stacks.TensorProduct.semilinearBasisTensorEquiv`.  Both
sides are the direct sum of copies of `M` indexed by the basis, and the map is the identity on
that description.

No finiteness of the index is used: the inverse is built from the `Finsupp` coordinates of a
section of `N'`, which are finitely supported for an arbitrary basis.

## Main definitions

* `Stacks.TensorProduct.semilinearTensorMap` — the map `N ⊗_R M ⟶ N' ⊗_{R'} M`, `n ⊗ m ↦ u n ⊗ m`.
  It needs only the semilinearity of `u`, no basis.
* `Stacks.TensorProduct.basisTensorInv` — its inverse, `n' ⊗ m ↦ Σ_i b i ⊗ (c.repr n' i) • m`.
* `Stacks.TensorProduct.semilinearBasisTensorEquiv` — **the identification**
  `N ⊗_R M ≃+ N' ⊗_{R'} M`.

## Main results

* `Stacks.TensorProduct.tmul_eq_sum_repr` — a pure tensor written through a basis of the left
  factor: `n ⊗ m = Σ_i b i ⊗ (b.repr n i) • m`.
* `Stacks.TensorProduct.bijective_semilinearTensorMap` — the map is bijective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.TensorProduct

universe uR uR' uN uN' uM uK

variable {R : Type uR} {R' : Type uR'} {N : Type uN} {N' : Type uN'} {M : Type uM} {K : Type uK}
  [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R' N']
  [AddCommGroup M] [Module R' M] [Module R M]

/-! ### The map across the base change -/

/-- The bilinear datum of `Stacks.TensorProduct.semilinearTensorMap`: a section `n` of `N` and a
section `m` of `M` go to the pure tensor `u n ⊗ m` of `N' ⊗_{R'} M`. -/
def semilinearTensorAux (u : N →+ N') : N →+ (M →+ N' ⊗[R'] M) :=
  AddMonoidHom.mk'
    (fun n ↦ AddMonoidHom.mk' (fun m ↦ u n ⊗ₜ[R'] m) fun m m' ↦ TensorProduct.tmul_add _ m m')
    fun n n' ↦ by
      refine AddMonoidHom.ext fun m ↦ ?_
      change u (n + n') ⊗ₜ[R'] m = u n ⊗ₜ[R'] m + u n' ⊗ₜ[R'] m
      rw [map_add, TensorProduct.add_tmul]

/-- **The map `N ⊗_R M ⟶ N' ⊗_{R'} M` of a semilinear map `u : N ⟶ N'`**, sending `n ⊗ m` to
`u n ⊗ m`. -/
def semilinearTensorMap {phi : R →+* R'} (u : N →+ N')
    (hu : ∀ (a : R) (n : N), u (a • n) = phi a • u n)
    (hM : ∀ (a : R) (m : M), a • m = phi a • m) :
    N ⊗[R] M →+ N' ⊗[R'] M :=
  TensorProduct.liftAddHom (semilinearTensorAux u) fun a n m ↦ by
    change u (a • n) ⊗ₜ[R'] m = u n ⊗ₜ[R'] (a • m)
    rw [hu, hM, TensorProduct.smul_tmul]

/-- `Stacks.TensorProduct.semilinearTensorMap` sends `n ⊗ m` to `u n ⊗ m`. -/
@[simp] theorem semilinearTensorMap_tmul {phi : R →+* R'} (u : N →+ N')
    (hu : ∀ (a : R) (n : N), u (a • n) = phi a • u n)
    (hM : ∀ (a : R) (m : M), a • m = phi a • m) (n : N) (m : M) :
    semilinearTensorMap u hu hM (n ⊗ₜ[R] m) = u n ⊗ₜ[R'] m :=
  rfl

/-! ### A pure tensor written through a basis of the left factor -/

/-- **A pure tensor written through a basis of the left factor**: `n ⊗ m` is the finite sum of the
`b i ⊗ (b.repr n i) • m` over the support of the coordinates of `n`. -/
theorem tmul_eq_sum_repr (b : Module.Basis K R N) (n : N) (m : M) :
    n ⊗ₜ[R] m = (b.repr n).sum fun i r ↦ b i ⊗ₜ[R] (r • m) := by
  conv_lhs => rw [← b.linearCombination_repr n]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul _ (b i) m

/-! ### The inverse, read off the coordinates of a section -/

/-- A pure tensor `x ⊗ (0 • m)` vanishes. -/
private theorem tmul_zero_smul {S : Type*} [Semiring S] [Module S M] (x : N) (m : M) :
    x ⊗ₜ[R] ((0 : S) • m) = 0 := by
  rw [zero_smul, TensorProduct.tmul_zero]

variable (b : Module.Basis K R N) (c : Module.Basis K R' N')

/-- The underlying function of `Stacks.TensorProduct.basisTensorInv`: a section `n'` of `N'` and a
section `m` of `M` go to `Σ_i b i ⊗ (c.repr n' i) • m`. -/
def basisTensorInvFun (n' : N') (m : M) : N ⊗[R] M :=
  (c.repr n').sum fun i r ↦ b i ⊗ₜ[R] (r • m)

/-- `Stacks.TensorProduct.basisTensorInvFun` is additive in the section of `N'`. -/
theorem basisTensorInvFun_add_left (n' n'' : N') (m : M) :
    basisTensorInvFun b c (n' + n'') m =
      basisTensorInvFun b c n' m + basisTensorInvFun b c n'' m := by
  have h : c.repr (n' + n'') = c.repr n' + c.repr n'' := map_add _ n' n''
  change (c.repr (n' + n'')).sum (fun i r ↦ b i ⊗ₜ[R] (r • m)) = _
  rw [h]
  exact Finsupp.sum_add_index' (fun i ↦ tmul_zero_smul _ _)
    fun i r r' ↦ by rw [add_smul, TensorProduct.tmul_add]

/-- `Stacks.TensorProduct.basisTensorInvFun` is additive in the section of `M`. -/
theorem basisTensorInvFun_add_right (n' : N') (m m' : M) :
    basisTensorInvFun b c n' (m + m') =
      basisTensorInvFun b c n' m + basisTensorInvFun b c n' m' := by
  change (∑ i ∈ (c.repr n').support, b i ⊗ₜ[R] ((c.repr n') i • (m + m'))) =
    (∑ i ∈ (c.repr n').support, b i ⊗ₜ[R] ((c.repr n') i • m)) +
      ∑ i ∈ (c.repr n').support, b i ⊗ₜ[R] ((c.repr n') i • m')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_add, TensorProduct.tmul_add]

/-- **The inverse of `Stacks.TensorProduct.semilinearTensorMap`**, read off the coordinates of a
section of `N'` in the basis `c`: `n' ⊗ m ↦ Σ_i b i ⊗ (c.repr n' i) • m`. -/
def basisTensorInv : N' ⊗[R'] M →+ N ⊗[R] M :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun n' ↦ AddMonoidHom.mk' (basisTensorInvFun b c n') (basisTensorInvFun_add_right b c n'))
      fun n' n'' ↦ AddMonoidHom.ext fun m ↦ basisTensorInvFun_add_left b c n' n'' m)
    fun r n' m ↦ by
      change basisTensorInvFun b c (r • n') m = basisTensorInvFun b c n' (r • m)
      change ((c.repr (r • n')).sum fun i s ↦ b i ⊗ₜ[R] (s • m)) =
        (c.repr n').sum fun i s ↦ b i ⊗ₜ[R] (s • (r • m))
      rw [map_smul, Finsupp.sum_smul_index' fun i ↦ by rw [zero_smul, TensorProduct.tmul_zero]]
      refine Finsupp.sum_congr fun i _ ↦ ?_
      rw [smul_eq_mul, smul_smul, mul_comm]

/-- `Stacks.TensorProduct.basisTensorInv` sends `n' ⊗ m` to `basisTensorInvFun b c n' m`. -/
@[simp] theorem basisTensorInv_tmul (n' : N') (m : M) :
    basisTensorInv b c (n' ⊗ₜ[R'] m) = basisTensorInvFun b c n' m :=
  rfl

/-- **The inverse at a basis vector of `N'`**: `basisTensorInvFun b c (c i) m = b i ⊗ m`. -/
theorem basisTensorInvFun_basis (i : K) (m : M) :
    basisTensorInvFun b c (c i) m = b i ⊗ₜ[R] m := by
  change ((c.repr (c i)).sum fun j r ↦ b j ⊗ₜ[R] (r • m)) = _
  rw [c.repr_self, Finsupp.sum_single_index (tmul_zero_smul _ _),
    one_smul]

/-! ### The two round trips -/

variable {phi : R →+* R'} {u : N →+ N'} (hu : ∀ (a : R) (n : N), u (a • n) = phi a • u n)
  (hM : ∀ (a : R) (m : M), a • m = phi a • m) (hc : ∀ i : K, c i = u (b i))

include hu hM hc

/-- The forward map sends `b i ⊗ m` to `c i ⊗ m`. -/
theorem semilinearTensorMap_basis_tmul (i : K) (m : M) :
    semilinearTensorMap (M := M) u hu hM (b i ⊗ₜ[R] m) = c i ⊗ₜ[R'] m := by
  rw [semilinearTensorMap_tmul, hc i]

/-- **The inverse undoes the forward map.** -/
theorem basisTensorInv_semilinearTensorMap (z : N ⊗[R] M) :
    basisTensorInv b c (semilinearTensorMap (M := M) u hu hM z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul n m =>
      rw [tmul_eq_sum_repr b n m, Finsupp.sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [semilinearTensorMap_basis_tmul b c hu hM hc, basisTensorInv_tmul,
        basisTensorInvFun_basis]
  | add x y hx hy => simp_all

/-- **The forward map undoes the inverse.** -/
theorem semilinearTensorMap_basisTensorInv (w : N' ⊗[R'] M) :
    semilinearTensorMap (M := M) u hu hM (basisTensorInv b c w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul n' m =>
      rw [basisTensorInv_tmul]
      change semilinearTensorMap (M := M) u hu hM
          ((c.repr n').sum fun i r ↦ b i ⊗ₜ[R] (r • m)) = _
      rw [Finsupp.sum, map_sum, tmul_eq_sum_repr c n' m, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ ↦ semilinearTensorMap_basis_tmul b c hu hM hc i _
  | add x y hx hy => simp_all

/-- **The map across the base change is bijective** as soon as the images of a basis of `N` form a
basis of `N'`. -/
theorem bijective_semilinearTensorMap :
    Function.Bijective (semilinearTensorMap (M := M) u hu hM) :=
  Function.bijective_iff_has_inverse.2
    ⟨basisTensorInv b c, basisTensorInv_semilinearTensorMap b c hu hM hc,
      semilinearTensorMap_basisTensorInv b c hu hM hc⟩

/-- **The identification `N ⊗_R M ≃+ N' ⊗_{R'} M`**, `n ⊗ m ↦ u n ⊗ m`, when the images under `u`
of a basis of `N` form a basis of `N'`. -/
def semilinearBasisTensorEquiv : N ⊗[R] M ≃+ N' ⊗[R'] M where
  toFun := semilinearTensorMap (M := M) u hu hM
  invFun := basisTensorInv b c
  left_inv := basisTensorInv_semilinearTensorMap b c hu hM hc
  right_inv := semilinearTensorMap_basisTensorInv b c hu hM hc
  map_add' := map_add (semilinearTensorMap (M := M) u hu hM)

/-- `Stacks.TensorProduct.semilinearBasisTensorEquiv` sends `n ⊗ m` to `u n ⊗ m`. -/
@[simp] theorem semilinearBasisTensorEquiv_tmul (n : N) (m : M) :
    semilinearBasisTensorEquiv b c hu hM hc (n ⊗ₜ[R] m) = u n ⊗ₜ[R'] m :=
  rfl

end Stacks.TensorProduct

end
