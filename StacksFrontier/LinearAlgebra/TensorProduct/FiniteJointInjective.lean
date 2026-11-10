module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

/-!
# A tensor product of two jointly injective finite families is jointly injective

Let `R` be a commutative ring, let `f i : M ⟶ M' i` be a family of maps which is *jointly
injective* — only `0` is carried to `0` by every member — and let `g j : N ⟶ N' j` be another.
Then the family `f i ⊗ g j : M ⊗_R N ⟶ M' i ⊗_R N' j` is jointly injective, provided the two
index types are **finite** and enough flatness is available.

Finiteness is not a convenience. The comparison
`(∏ᵢ M' i) ⊗ (∏ⱼ N' j) ⟶ ∏ᵢⱼ (M' i ⊗ N' j)` is an isomorphism only for finite index types —
that is `TensorProduct.piRight`, which carries `[Fintype]` — and for infinite ones the conclusion
is false: for `M = N = ∏_{n : ℕ} R` with the two families of projections, a tensor product of two
infinite products is strictly smaller than the product of the pairwise tensor products, so there
is nothing to force an element to be detected by the pairwise projections.

## Main results

* `TensorProduct.eq_zero_of_lTensor_proj` and `TensorProduct.eq_zero_of_rTensor_proj`: an element
  of `M ⊗ ∏ⱼ N j`, respectively of `(∏ᵢ M i) ⊗ N`, killed by every projection in the family
  variable is zero.
* `TensorProduct.eq_zero_of_map_proj`: an element of `(∏ᵢ M i) ⊗ (∏ⱼ N j)` killed by every
  `proj i ⊗ proj j` is zero.
* `TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective`: **the conclusion** — for finite
  index types, an element of `M ⊗_R N` killed by every `f i ⊗ g j` is zero.

## Implementation notes

The one-sided statement on the right is read off `TensorProduct.piRight`, whose `j`-th component
is `LinearMap.lTensor _ (LinearMap.proj j)`; Mathlib records that only on pure tensors, as
`TensorProduct.piRightHom_tmul`, so it is proved here by induction. The left-hand version is the
right-hand one conjugated by `TensorProduct.comm`.

Finiteness is carried as `Finite` and turned into the `Fintype` and `DecidableEq` that
`TensorProduct.piRight` wants inside the proof, so that no statement mentions data a consumer
would have to match.

`TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective` carries its flatness as the two
instance arguments `Module.Flat R (∀ i, M' i)` and `Module.Flat R N` that
`TensorProduct.map_injective_of_flat_flat` consumes. Over a field every module is flat, so a
consumer working over a field discharges them once `Module.Free.of_divisionRing` and
`Module.Flat.of_free` are available as instances.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} [CommRing R]

/-! ### The components of the comparison with a product -/

section Components

variable {M : Type v} [AddCommGroup M] [Module R M]
  {J : Type w} {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- The `j`-th component of `TensorProduct.piRightHom` is
`LinearMap.lTensor _ (LinearMap.proj j)`. -/
theorem piRightHom_apply_eq_lTensor_proj (w : M ⊗[R] (∀ j, N j)) (j : J) :
    piRightHom R R M N w j = LinearMap.lTensor M (LinearMap.proj j) w := by
  induction w using TensorProduct.inductionOn with
  | tmul x f => simp
  | add w w' hw hw' => simp [hw, hw']

end Components

section CommComponents

variable {N : Type v} [AddCommGroup N] [Module R N]
  {I : Type w} {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Projecting the left factor commutes with the symmetry of the tensor product. -/
theorem lTensor_proj_comm_apply (i : I) (w : (∀ i, M i) ⊗[R] N) :
    LinearMap.lTensor N (LinearMap.proj i) (TensorProduct.comm R (∀ i, M i) N w)
      = TensorProduct.comm R (M i) N (LinearMap.rTensor N (LinearMap.proj i) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => simp
  | add w w' hw hw' => simp [hw, hw']

end CommComponents

section BothComponents

variable {I J : Type*}
  {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- Projecting the two factors one at a time is projecting them together. -/
theorem lTensor_rTensor_proj_apply (i : I) (j : J) (w : (∀ i, M i) ⊗[R] (∀ j, N j)) :
    LinearMap.lTensor (M i) (LinearMap.proj j)
        (LinearMap.rTensor (∀ j, N j) (LinearMap.proj i) w)
      = TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) w := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => simp
  | add w w' hw hw' => simp [hw, hw']

end BothComponents

/-! ### Detection by the projections -/

section Right

variable {M : Type v} [AddCommGroup M] [Module R M]
  {J : Type w} [Finite J] {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- **An element of `M ⊗ ∏ⱼ N j` killed by every projection is zero**, for a finite index
type. -/
theorem eq_zero_of_lTensor_proj (w : M ⊗[R] (∀ j, N j))
    (h : ∀ j, LinearMap.lTensor M (LinearMap.proj j) w = 0) : w = 0 := by
  classical
  let _ := Fintype.ofFinite J
  refine (piRight R R M N).injective ?_
  rw [map_zero]
  funext j
  rw [piRight_apply, piRightHom_apply_eq_lTensor_proj]
  exact h j

end Right

section Left

variable {N : Type v} [AddCommGroup N] [Module R N]
  {I : Type w} [Finite I] {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **An element of `(∏ᵢ M i) ⊗ N` killed by every projection is zero**, for a finite index
type. -/
theorem eq_zero_of_rTensor_proj (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, LinearMap.rTensor N (LinearMap.proj i) w = 0) : w = 0 := by
  refine (TensorProduct.comm R (∀ i, M i) N).injective ?_
  rw [map_zero]
  refine eq_zero_of_lTensor_proj _ fun i => ?_
  rw [lTensor_proj_comm_apply, h i, map_zero]

end Left

section Both

variable {I J : Type*} [Finite I] [Finite J]
  {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- **An element of `(∏ᵢ M i) ⊗ (∏ⱼ N j)` killed by every `proj i ⊗ proj j` is zero**, for finite
index types. -/
theorem eq_zero_of_map_proj (w : (∀ i, M i) ⊗[R] (∀ j, N j))
    (h : ∀ i j, TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) w = 0) : w = 0 := by
  refine eq_zero_of_rTensor_proj _ fun i => eq_zero_of_lTensor_proj _ fun j => ?_
  rw [lTensor_rTensor_proj_apply]
  exact h i j

end Both

/-! ### The conclusion -/

section Conclusion

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {I J : Type*}
  {M' : I → Type*} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
  {N' : J → Type*} [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)]

/-- Projecting a tensor product of two `LinearMap.pi`s is the tensor product of the two
components. -/
theorem map_proj_map_pi_apply (f : ∀ i, M →ₗ[R] M' i) (g : ∀ j, N →ₗ[R] N' j) (i : I) (j : J)
    (z : M ⊗[R] N) :
    TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)
        (TensorProduct.map (LinearMap.pi f) (LinearMap.pi g) z)
      = TensorProduct.map (f i) (g j) z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add z z' hz hz' => simp [hz, hz']

/-- A family of maps of which only `0` is killed by every member has injective `LinearMap.pi`. -/
private theorem injective_pi_of_forall_eq_zero {A : Type*} [AddCommGroup A] [Module R A]
    {K : Type*} {B : K → Type*} [∀ k, AddCommGroup (B k)] [∀ k, Module R (B k)]
    (f : ∀ k, A →ₗ[R] B k) (hf : ∀ x : A, (∀ k, f k x = 0) → x = 0) :
    Function.Injective (LinearMap.pi f) :=
  (injective_iff_map_eq_zero _).2 fun x hx => hf x fun k => congrFun hx k

/-- **A tensor product of two jointly injective finite families is jointly injective.** If only
`0 : M` is killed by every `f i` and only `0 : N` by every `g j`, then only `0 : M ⊗_R N` is
killed by every `f i ⊗ g j` — provided the two index types are finite. -/
theorem eq_zero_of_map_eq_zero_of_jointly_injective [Finite I] [Finite J]
    [Module.Flat R (∀ i, M' i)] [Module.Flat R N]
    (f : ∀ i, M →ₗ[R] M' i) (g : ∀ j, N →ₗ[R] N' j)
    (hf : ∀ x : M, (∀ i, f i x = 0) → x = 0) (hg : ∀ y : N, (∀ j, g j y = 0) → y = 0)
    (z : M ⊗[R] N) (h : ∀ i j, TensorProduct.map (f i) (g j) z = 0) : z = 0 := by
  refine (TensorProduct.map_injective_of_flat_flat (LinearMap.pi f) (LinearMap.pi g)
    (injective_pi_of_forall_eq_zero f hf) (injective_pi_of_forall_eq_zero g hg)) ?_
  rw [map_zero]
  refine eq_zero_of_map_proj _ fun i j => ?_
  rw [map_proj_map_pi_apply]
  exact h i j

end Conclusion

end TensorProduct

end
