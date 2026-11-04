module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-! # `LinearMap.toAddMonoidHom` is additive

Two `rfl` lemmas letting `simp` push `LinearMap.toAddMonoidHom` through `0` and `+`.

Mathlib bundles the same content as `LinearMap.toAddMonoidHom'`, the additive monoid hom
`(M →ₛₗ[σ₁₂] M₂) →+ (M →+ M₂)`, from which these are `map_zero` and `map_add`. Neither is
available as a standalone `simp` lemma, though, so a goal mentioning `(f + g).toAddMonoidHom`
does not simplify on its own — which is what these are for.
-/

@[expose] public section

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

@[simp]
theorem LinearMap.zero_toAddMonoidHom : (0 : M →ₗ[R] N).toAddMonoidHom = 0 := rfl

theorem LinearMap.add_toAddMonoidHom (f g : M →ₗ[R] N) :
    (f + g).toAddMonoidHom = f.toAddMonoidHom + g.toAddMonoidHom := rfl
