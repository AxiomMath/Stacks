module

public import Mathlib.RingTheory.IsTensorProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of universal bilinear pairs

Let `R` be a commutative ring and `M`, `N` be `R`-modules. A pair `(T, g)` of an `R`-module `T`
and an `R`-bilinear map `g : M × N → T` is *universal* if every `R`-bilinear map
`f : M × N → P` factors as `f = f̃ ∘ g` for a unique `R`-linear map `f̃ : T → P`. Mathlib's
`TensorProduct.lift`, `TensorProduct.lift.tmul` and `TensorProduct.lift.unique` say that
`(M ⊗[R] N, TensorProduct.mk R M N)` is such a pair. This file proves the second half of
Stacks 00CX: two universal pairs `(T, g)` and `(T', g')` are related by a unique `R`-linear
isomorphism `j : T ≃ T'` with `j ∘ g = g'`.

A bilinear map `M × N → T` is encoded as `g : M →ₗ[R] N →ₗ[R] T`, and the composite `j ∘ g` as
`g.compr₂ j`.

## Main results

* `TensorProduct.existsUnique_linearEquiv_compr₂_eq_of_universal` — uniqueness up to unique
  isomorphism for pairs given by the universal property itself.
* `IsTensorProduct.existsUnique_linearEquiv_compr₂_eq` — the same for pairs given by Mathlib's
  predicate `IsTensorProduct` (the induced map from `M ⊗[R] N` is bijective).
-/

@[expose] public section

add_to_stacks 00CX "The factorization identity `f = f̃ ∘ g`: `TensorProduct.lift f` composed
  with `m ⊗ₜ n` is `f m n`." TensorProduct.lift.tmul

universe w

namespace TensorProduct

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- **Stacks 00CX** (uniqueness). If `(T, g)` and `(T', g')` are two pairs of an `R`-module and an
`R`-bilinear map `M × N → _` which both have the universal property (every bilinear map `f` to an
`R`-module `P` is `f̃ ∘ g` for a unique linear `f̃`), then there is a unique `R`-linear isomorphism
`j : T ≃ T'` with `j ∘ g = g'`. The universal property is quantified over modules `P` in the
universe of `T` and `T'`. -/
@[stacks 00CX "Uniqueness: two universal pairs `(T, g)`, `(T', g')` admit a unique isomorphism
`j : T ≃ T'` with `j ∘ g = g'`; the universal property quantifies over modules in the universe of
`T` and `T'`."]
theorem existsUnique_linearEquiv_compr₂_eq_of_universal {T T' : Type w} [AddCommGroup T]
    [Module R T] [AddCommGroup T'] [Module R T'] (g : M →ₗ[R] N →ₗ[R] T)
    (g' : M →ₗ[R] N →ₗ[R] T')
    (hg : ∀ (P : Type w) [AddCommGroup P] [Module R P] (f : M →ₗ[R] N →ₗ[R] P),
      ∃! f' : T →ₗ[R] P, g.compr₂ f' = f)
    (hg' : ∀ (P : Type w) [AddCommGroup P] [Module R P] (f : M →ₗ[R] N →ₗ[R] P),
      ∃! f' : T' →ₗ[R] P, g'.compr₂ f' = f) :
    ∃! j : T ≃ₗ[R] T', g.compr₂ j.toLinearMap = g' := by
  obtain ⟨j, hj, -⟩ := hg T' g'
  obtain ⟨j', hj', -⟩ := hg' T g
  obtain ⟨_, -, hT⟩ := hg T g
  obtain ⟨_, -, hT'⟩ := hg' T' g'
  have h₁ : j' ∘ₗ j = LinearMap.id :=
    (hT _ (show g.compr₂ (j' ∘ₗ j) = g by rw [LinearMap.compr₂_comp, hj, hj'])).trans
      (hT _ (LinearMap.compr₂_id g)).symm
  have h₂ : j ∘ₗ j' = LinearMap.id :=
    (hT' _ (show g'.compr₂ (j ∘ₗ j') = g' by rw [LinearMap.compr₂_comp, hj', hj])).trans
      (hT' _ (LinearMap.compr₂_id g')).symm
  refine ⟨LinearEquiv.ofLinearMap j j' h₂ h₁, hj, fun φ hφ => ?_⟩
  obtain ⟨_, -, hu⟩ := hg T' g'
  exact LinearEquiv.toLinearMap_injective ((hu _ hφ).trans (hu _ hj).symm)

end TensorProduct

namespace IsTensorProduct

variable {R : Type*} [CommRing R] {M N T T' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T] [AddCommGroup T'] [Module R T']

/-- **Stacks 00CX** (uniqueness, for `IsTensorProduct`). If `g : M × N → T` and `g' : M × N → T'`
are bilinear maps exhibiting `T` and `T'` as tensor products of `M` and `N` (Mathlib's
`IsTensorProduct`), then there is a unique `R`-linear isomorphism `j : T ≃ T'` with
`j ∘ g = g'`. -/
@[stacks 00CX "Uniqueness, for pairs exhibited as tensor products by `IsTensorProduct`: there is
a unique isomorphism `j : T ≃ T'` with `j ∘ g = g'`."]
theorem existsUnique_linearEquiv_compr₂_eq {g : M →ₗ[R] N →ₗ[R] T} {g' : M →ₗ[R] N →ₗ[R] T'}
    (hg : IsTensorProduct g) (hg' : IsTensorProduct g') :
    ∃! j : T ≃ₗ[R] T', g.compr₂ j.toLinearMap = g' := by
  refine ⟨hg.equiv.symm.trans hg'.equiv, ?_, fun φ hφ => ?_⟩
  · ext m n
    simp [IsTensorProduct.equiv_symm_apply, IsTensorProduct.equiv_apply]
  · have key : φ.toLinearMap ∘ₗ hg.equiv.toLinearMap = hg'.equiv.toLinearMap := by
      apply TensorProduct.ext'
      intro m n
      have := congrArg (fun F => F m n) hφ
      simpa using this
    ext x
    obtain ⟨y, rfl⟩ := hg.equiv.surjective x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun key y

end IsTensorProduct
