module

public import Mathlib.FieldTheory.Normal.Basic

/-!
# Restricting and extending automorphisms in a tower of fields

Let `L / M / K` be a tower of field extensions. Stacks 0BME says:

1. if `M / K` is normal, every automorphism `τ` of `L / K` maps `M` into itself and so induces
   an automorphism `τ|_M` of `M / K`;
2. if `L / K` is normal, every `K`-algebra map `σ : M → L` extends to an automorphism of `L / K`.

Mathlib's `AlgEquiv.restrictNormal` and `AlgHom.liftNormal` construct these maps; the two
theorems below state the properties themselves.

## Main results

* `AlgEquiv.exists_algEquiv_algebraMap_eq_of_normal`: part (1).
* `AlgHom.exists_algEquiv_extending_of_normal`: part (2).
-/

@[expose] public section

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra K L]
  [Algebra M L] [IsScalarTower K M L]

/-- **Stacks 0BME (1).** Let `L / M / K` be a tower of fields with `M / K` normal. Then every
automorphism `τ` of `L / K` induces an automorphism `τ|_M` of `M / K`, that is, an automorphism
of `M / K` through which `τ` acts on the image of `M` in `L`. No algebraicity of `L / K` is
needed. -/
@[stacks 0BME "(1): an automorphism of `L / K` restricts to an automorphism of `M` when `M / K`
is normal"]
theorem AlgEquiv.exists_algEquiv_algebraMap_eq_of_normal [Normal K M] (τ : L ≃ₐ[K] L) :
    ∃ τM : M ≃ₐ[K] M, ∀ m : M, algebraMap M L (τM m) = τ (algebraMap M L m) :=
  ⟨τ.restrictNormal M, fun m => τ.restrictNormal_commutes M m⟩

/-- **Stacks 0BME (2).** Let `L / M / K` be a tower of fields with `L / K` normal. Then every
`K`-algebra map `σ : M → L` extends to an automorphism of `L / K`, that is, an automorphism
`τ` of `L / K` with `τ ∘ (M → L) = σ`. -/
@[stacks 0BME "(2): a `K`-algebra map `M → L` extends to an automorphism of `L` when `L / K`
is normal"]
theorem AlgHom.exists_algEquiv_extending_of_normal [Normal K L] (σ : M →ₐ[K] L) :
    ∃ τ : L ≃ₐ[K] L, ∀ m : M, τ (algebraMap M L m) = σ m :=
  ⟨AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _),
    fun m => σ.liftNormal_commutes L m⟩

end
