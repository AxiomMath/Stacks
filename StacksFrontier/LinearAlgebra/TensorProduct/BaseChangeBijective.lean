module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Bijectivity of a map out of a tensor product, transported along its right factor

Let `R` be a commutative semiring, let `M₀` be an `R`-module, and consider two additive maps out
of a tensor product with `M₀` on the left,

`f : M₀ ⊗_R M ⟶ M₁`,  `g : M₀ ⊗_R N ⟶ N₁`,

whose targets carry no structure beyond their addition.  Suppose given an `R`-linear equivalence
`e : M ≃ N` of the right factors and an additive equivalence `e₁ : M₁ ≃ N₁` of the targets with
`g (t ⊗ e s) = e₁ (f (t ⊗ s))` for every pure tensor.  Then `f` is bijective exactly when `g` is.

The two maps are then conjugate: `g = e₁ ∘ f ∘ (e.lTensor M₀).symm`, the equivalence
`e.lTensor M₀ : M₀ ⊗_R M ≃ M₀ ⊗_R N` being `TensorProduct.congr (LinearEquiv.refl R M₀) e`.  The
compatibility is asked for only on pure tensors, which is all a construction on a tensor product
ever supplies, and it is extended to the whole tensor product by
`TensorProduct.apply_lTensor_of_tmul_comm`.

The maps are additive maps and not linear ones because this is written for a *base change*: `M₀`
is a ring extending the scalars, `M₁` and `N₁` are modules over that extension and not over `R`,
and the compatibility with the extended scalars is carried by the hypothesis on pure tensors
rather than by the types.  `TensorProduct.congr` transports the two factors of a tensor product
over a fixed base, and `Function.Bijective.of_comp_iff` transports bijectivity along a bijection;
what is not in Mathlib is this combination, which is the form in which a map defined on a base
change by its values on pure tensors is compared with another such map.

## Main results

* `TensorProduct.apply_lTensor_of_tmul_comm` — the compatibility on pure tensors holds on every
  element of the tensor product.
* `TensorProduct.bijective_iff_of_tmul_comm` — **bijectivity transports**: the two maps are
  bijective together.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {R M₀ M N M₁ N₁ : Type*} [CommSemiring R] [AddCommMonoid M₀] [Module R M₀]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid M₁]
  [AddCommMonoid N₁]

/-- **The compatibility of two maps out of a base change, on every element.**  If
`g (t ⊗ e s) = e₁ (f (t ⊗ s))` on pure tensors then `g ∘ (𝟙 ⊗ e) = e₁ ∘ f`, both sides being
additive in the element of the tensor product. -/
theorem apply_lTensor_of_tmul_comm {f : M₀ ⊗[R] M →+ M₁} {g : M₀ ⊗[R] N →+ N₁} {e : M ≃ₗ[R] N}
    {e₁ : M₁ ≃+ N₁} (h : ∀ (t : M₀) (s : M), g (t ⊗ₜ[R] e s) = e₁ (f (t ⊗ₜ[R] s)))
    (z : M₀ ⊗[R] M) : g (e.lTensor M₀ z) = e₁ (f z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul t s => rw [LinearEquiv.lTensor_tmul, h]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **Bijectivity of a map out of a base change is transported by an equivalence of the right
factor and an equivalence of the target.**

Only the values on pure tensors are compared, and the targets are compared by an additive
equivalence alone: the hypothesis `h` is what carries whatever semilinearity the two maps have.
-/
theorem bijective_iff_of_tmul_comm {f : M₀ ⊗[R] M →+ M₁} {g : M₀ ⊗[R] N →+ N₁} (e : M ≃ₗ[R] N)
    (e₁ : M₁ ≃+ N₁) (h : ∀ (t : M₀) (s : M), g (t ⊗ₜ[R] e s) = e₁ (f (t ⊗ₜ[R] s))) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← EquivLike.comp_bijective f e₁, ← EquivLike.bijective_comp (e.lTensor M₀) g]
  exact iff_of_eq (congrArg _ (funext (apply_lTensor_of_tmul_comm h)).symm)

end TensorProduct

end
