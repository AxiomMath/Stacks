module

public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# A tensor product of two finite products, read component by component

Let `R` be a commutative ring and let `A i` and `B j` be two **finite** families of `R`-modules.
The comparison

`(∏ᵢ A i) ⊗_R (∏ⱼ B j) ⟶ ∏ᵢⱼ (A i ⊗_R B j)`,  `w ↦ (proj i ⊗ proj j) w`

is then an isomorphism, so a family of elements of the `A i ⊗ B j` assembles into one element of
the tensor product of the two products. That is the statement below, in the form a consumer uses
it: every family is hit. Finiteness is essential — it is `TensorProduct.piRight` that is being
composed with itself, and for an infinite family the comparison is only injective.

Alongside it are the few component identities that make such an assembled element usable: how
`TensorProduct.map` interacts with a difference in either argument, with `LinearMap.rTensor` and
`LinearMap.lTensor` of a map into a product, and with a composite in either argument.

## Main results

* `TensorProduct.exists_map_proj_eq`: **every family of elements of the `A i ⊗ B j` comes from an
  element of `(∏ᵢ A i) ⊗ (∏ⱼ B j)`**, for finite index types.
* `TensorProduct.map_sub_left` and `TensorProduct.map_sub_right`: `TensorProduct.map` is
  subtractive in each argument.
* `TensorProduct.map_proj_rTensor_apply` and `TensorProduct.map_proj_lTensor_apply`: projecting
  the image of `LinearMap.rTensor`, respectively `LinearMap.lTensor`, of a map into a product.
* `TensorProduct.map_comp_apply`: composites in the two arguments of `TensorProduct.map` may be
  applied in two steps.

## Implementation notes

`TensorProduct.piRight` carries `[Fintype]` and `[DecidableEq]`, which are data; the statement of
`TensorProduct.exists_map_proj_eq` carries only `[Finite]`, and the two instances are introduced
inside its proof, so that nothing a consumer has to match mentions a choice of enumeration.

The equivalence itself is not named. Its two halves are `TensorProduct.piRight` conjugated by
`TensorProduct.comm`, and the only fact anybody needs about it is that its `(i, j)` component is
`proj i ⊗ proj j`, which is what the existence statement records.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TensorProduct

variable {R : Type*} [CommRing R]

section Components

variable {A A' A'' B B' B'' : Type*} [AddCommGroup A] [Module R A] [AddCommGroup A']
  [Module R A'] [AddCommGroup A''] [Module R A''] [AddCommGroup B] [Module R B]
  [AddCommGroup B'] [Module R B'] [AddCommGroup B''] [Module R B'']

/-- `TensorProduct.map` is subtractive in its first argument. -/
theorem map_sub_left (u u' : A →ₗ[R] A') (q : B →ₗ[R] B') (w : A ⊗[R] B) :
    map (u - u') q w = map u q w - map u' q w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.sub_tmul]
  | add w w' hw hw' =>
    rw [map_add, map_add, map_add, hw, hw']
    abel

/-- `TensorProduct.map` is subtractive in its second argument. -/
theorem map_sub_right (u : A →ₗ[R] A') (q q' : B →ₗ[R] B') (w : A ⊗[R] B) :
    map u (q - q') w = map u q w - map u q' w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.tmul_sub]
  | add w w' hw hw' =>
    rw [map_add, map_add, map_add, hw, hw']
    abel

/-- Composites in the two arguments of `TensorProduct.map` may be applied in two steps. -/
theorem map_comp_apply (u : A' →ₗ[R] A'') (v : B' →ₗ[R] B'') (pa : A →ₗ[R] A')
    (qb : B →ₗ[R] B') (w : A ⊗[R] B) :
    map u v (map pa qb w) = map (u ∘ₗ pa) (v ∘ₗ qb) w := by
  rw [map_comp]
  rfl

variable {K : Type*} {C : K → Type*} [∀ κ, AddCommGroup (C κ)] [∀ κ, Module R (C κ)]

/-- Projecting the image of `LinearMap.rTensor` of a map into a product. -/
theorem map_proj_rTensor_apply (d : A →ₗ[R] ∀ κ, C κ) (q : B →ₗ[R] B') (κ : K)
    (w : A ⊗[R] B) :
    map (LinearMap.proj κ) q (d.rTensor B w) = map (LinearMap.proj κ ∘ₗ d) q w := by
  rw [LinearMap.rTensor_def, map_comp_apply, LinearMap.comp_id]

/-- Projecting the image of `LinearMap.lTensor` of a map into a product. -/
theorem map_proj_lTensor_apply (d : B →ₗ[R] ∀ κ, C κ) (p : A →ₗ[R] A') (κ : K)
    (w : A ⊗[R] B) :
    map p (LinearMap.proj κ) (d.lTensor A w) = map p (LinearMap.proj κ ∘ₗ d) w := by
  rw [LinearMap.lTensor_def, map_comp_apply, LinearMap.comp_id]

end Components

section Grid

variable {I J : Type*} {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  {B : J → Type*} [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]

/-- **Every family of elements of the `A i ⊗ B j` comes from one element of
`(∏ᵢ A i) ⊗ (∏ⱼ B j)`**, for finite index types. -/
theorem exists_map_proj_eq [Finite I] [Finite J] (z : ∀ i, ∀ j, A i ⊗[R] B j) :
    ∃ w : (∀ i, A i) ⊗[R] (∀ j, B j),
      ∀ i j, TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) w = z i j := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let e : ((∀ i, A i) ⊗[R] (∀ j, B j)) ≃ₗ[R] ∀ i, ∀ j, (A i ⊗[R] B j) :=
    (TensorProduct.comm R _ _).trans
      ((TensorProduct.piRight R R (∀ j, B j) A).trans
        (LinearEquiv.piCongrRight fun i =>
          (TensorProduct.comm R (∀ j, B j) (A i)).trans (TensorProduct.piRight R R (A i) B)))
  obtain ⟨w, rfl⟩ := e.surjective z
  refine ⟨w, fun i j => ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [e]
  | add w w' hw hw' => simp [hw, hw']

end Grid

end TensorProduct

end
