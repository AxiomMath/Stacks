module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor–Hom equivalence

Let `R` be a commutative ring and let `K`, `L`, `M` be `R`-modules. Currying identifies an
`R`-bilinear description of a map out of `K ⊗_R L` with an iterated Hom module: the canonical
map `Hom_R(K, Hom_R(L, M)) ≃ Hom_R(K ⊗_R L, M)` sends `f` to the unique linear map taking
`x ⊗ y` to `f(x)(y)`. Mathlib already has this equivalence as `TensorProduct.lift.equiv`, in the
more general semilinear form; this file records it under a conceptual name and spells out its
action on pure tensors in both directions.

## Main definitions

* `StacksDraft.TensorHomEquiv.tensorHomEquiv` ([stacks 0A5Z]): the tensor–Hom equivalence, an
  abbreviation for Mathlib's `TensorProduct.lift.equiv`.

## Main results

* `StacksDraft.TensorHomEquiv.tensorHomEquiv_apply` ([stacks 0A5Z]): the equivalence sends
  `f : K →ₗ[R] L →ₗ[R] M` to the map `x ⊗ y ↦ f x y`.
* `StacksDraft.TensorHomEquiv.tensorHomEquiv_symm_apply` ([stacks 0A5Z]): its inverse sends
  `g : K ⊗[R] L →ₗ[R] M` to the map `x ↦ y ↦ g (x ⊗ y)`.

## Implementation notes

The equality of Hom modules asserted by the source is realized here as a genuine `R`-linear
equivalence rather than an equality of types, which is the only faithful reading in a
type-theoretic setting. Since Mathlib supplies the underlying content, the definition is an
alias; the two component formulas are what make the module state something checkable about it,
and together with the alias they form the covering set for the tag. Both hold by `rfl`, because
`TensorProduct.lift.equiv` is built from `TensorProduct.uncurry` and `TensorProduct.mk`.

Mathlib states the equivalence for a ring homomorphism `σ₁₂ : R →+* R₂` and `σ₁₂`-semilinear
maps; the source statement is the `R`-linear case, obtained by taking `σ₁₂ = RingHom.id R`, and
that is the case the component formulas below are stated in. The three modules are allowed to
live in different universes, as they do in Mathlib.

## References

* [The Stacks Project, Tag 0A5Z](https://stacks.math.columbia.edu/tag/0A5Z)
-/

@[expose] public section

open scoped TensorProduct

namespace StacksDraft.TensorHomEquiv

/-- **Stacks 0A5Z.** Linear maps into a module of linear maps are canonically equivalent to
linear maps out of the corresponding tensor product: `Hom_R(K, Hom_R(L, M))` is identified with
`Hom_R(K ⊗_R L, M)` by sending `f` to the map determined by `x ⊗ y ↦ f(x)(y)`. -/
@[stacks 0A5Z, stacks_fixed 0A5Z]
alias tensorHomEquiv := TensorProduct.lift.equiv

/-- **Stacks 0A5Z.** The tensor–Hom equivalence sends `f : K →ₗ[R] L →ₗ[R] M` to the linear map
taking the pure tensor `x ⊗ y` to `f x y`. -/
@[stacks 0A5Z, stacks_fixed 0A5Z, simp]
theorem tensorHomEquiv_apply {R : Type*} [CommRing R] (K L M : Type*)
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module R K] [Module R L] [Module R M]
    (f : K →ₗ[R] L →ₗ[R] M) (x : K) (y : L) :
    tensorHomEquiv (RingHom.id R) K L M f (x ⊗ₜ[R] y) = f x y :=
  rfl

/-- **Stacks 0A5Z.** The inverse of the tensor–Hom equivalence sends `g : K ⊗[R] L →ₗ[R] M` to
the map `x ↦ y ↦ g (x ⊗ y)`. -/
@[stacks 0A5Z, stacks_fixed 0A5Z, simp]
theorem tensorHomEquiv_symm_apply {R : Type*} [CommRing R] (K L M : Type*)
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module R K] [Module R L] [Module R M]
    (g : K ⊗[R] L →ₗ[R] M) (x : K) (y : L) :
    ((tensorHomEquiv (RingHom.id R) K L M).symm g) x y = g (x ⊗ₜ[R] y) :=
  rfl

end StacksDraft.TensorHomEquiv

end
