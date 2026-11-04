module

public import StacksFrontier.Homology.KFlat.TensorExactAbove
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Top-degree cycles of a bounded complex of flat modules commute with tensor products

Let `C⁰ → C¹ → ⋯` be a sequence of flat `R`-modules and linear maps `δⁱ : Cⁱ → Cⁱ⁺¹` which
vanishes from some degree on and is exact in every degree `> d`. Then every boundary module
`Im(δⁱ)`, `i ≥ d`, is flat: descending from the top, `Im(δⁱ) = Ker(δⁱ⁺¹)` is the kernel of the
surjection `Cⁱ⁺¹ ↠ Im(δⁱ⁺¹)` between flat modules. Consequently, for every `R`-module `N`, the
cycles in degree `d` commute with `N ⊗_R -`:

`N ⊗_R Ker(δᵈ) ≅ Ker(N ⊗ δᵈ)`,

because `0 → Ker(δᵈ) → Cᵈ → Im(δᵈ) → 0` and `0 → Im(δᵈ) → Cᵈ⁺¹ → Im(δᵈ⁺¹) → 0` are short exact
with flat right-hand terms. In cohomological language: `Hᵈ(N ⊗ C) = N ⊗ Hᵈ(C)`.

## Main results

* `Stacks.FlatComplexTopDegree.flat_range`: the boundaries above `d` are flat.
* `Stacks.FlatComplexTopDegree.lTensor_ker_subtype_injective`: `N ⊗ Ker(δᵈ) → N ⊗ Cᵈ` is
  injective.
* `Stacks.FlatComplexTopDegree.range_lTensor_ker_subtype`: its image is `Ker(N ⊗ δᵈ)`.
-/

@[expose] public section

universe u v

namespace Stacks.FlatComplexTopDegree

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ i, AddCommGroup (C i)]
  [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)] (δ : ∀ i, C i →ₗ[R] C (i + 1)) (d n : ℕ)
  (hn : ∀ i, n ≤ i → Subsingleton (C i))
  (hex : ∀ i, d ≤ i → Function.Exact (δ i) (δ (i + 1)))

include hn hex in
/-- **The boundaries of a bounded complex of flat modules exact above `d` are flat above `d`.** -/
theorem flat_range (i : ℕ) (hi : d ≤ i) : Module.Flat R (LinearMap.range (δ i)) := by
  suffices h : ∀ m i, d ≤ i → n ≤ i + 1 + m → Module.Flat R (LinearMap.range (δ i)) from
    h n i hi (by omega)
  intro m
  induction m with
  | zero =>
    intro i _ hni
    have := hn (i + 1) (by omega)
    have : Subsingleton (LinearMap.range (δ i)) := inferInstance
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofSubsingleton (Fin 0 →₀ R) _).symm
  | succ m ih =>
    intro i hdi hni
    have := ih (i + 1) (by omega) (by omega)
    have hk : Module.Flat R (LinearMap.ker (δ (i + 1)).rangeRestrict) :=
      CochainComplex.KFlat.flat_ker_of_surjective _ (δ (i + 1)).surjective_rangeRestrict
    rw [LinearMap.ker_rangeRestrict, (LinearMap.exact_iff.1 (hex i hdi))] at hk
    exact hk

/-- `N ⊗ S → N ⊗ M` is injective for `S = Ker f` when `Im f` is flat. -/
private theorem lTensor_subtype_injective_of_flat_range {M P : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (S : Submodule R M)
    (hS : LinearMap.ker f = S) [Module.Flat R (LinearMap.range f)] (N : Type*) [AddCommGroup N]
    [Module R N] : Function.Injective (S.subtype.lTensor N) := by
  refine LinearMap.lTensor_injective_of_exact_of_flat f.rangeRestrict
    f.surjective_rangeRestrict _ S.injective_subtype ?_ N
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, hS, Submodule.range_subtype]

include hn hex in
/-- **`N ⊗ Ker(δᵈ) → N ⊗ Cᵈ` is injective**, for every `R`-module `N`. -/
theorem lTensor_ker_subtype_injective (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective ((LinearMap.ker (δ d)).subtype.lTensor N) := by
  have := flat_range δ d n hn hex d le_rfl
  exact lTensor_subtype_injective_of_flat_range (δ d) _ rfl N

include hn hex in
/-- **The cycles of `N ⊗ C` in degree `d` are `N ⊗ Ker(δᵈ)`**: the image of
`N ⊗ Ker(δᵈ) → N ⊗ Cᵈ` is the kernel of `N ⊗ δᵈ`. -/
theorem range_lTensor_ker_subtype (N : Type*) [AddCommGroup N] [Module R N] :
    LinearMap.range ((LinearMap.ker (δ d)).subtype.lTensor N) =
      LinearMap.ker ((δ d).lTensor N) := by
  have := flat_range δ d n hn hex (d + 1) (by omega)
  have hinj : Function.Injective ((LinearMap.range (δ d)).subtype.lTensor N) :=
    lTensor_subtype_injective_of_flat_range (δ (d + 1)) _
      (LinearMap.exact_iff.1 (hex d le_rfl)) N
  have hcomp : (δ d).lTensor N =
      ((LinearMap.range (δ d)).subtype.lTensor N) ∘ₗ ((δ d).rangeRestrict.lTensor N) := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hinj)]
  refine (LinearMap.exact_iff.1 (lTensor_exact N ?_ (δ d).surjective_rangeRestrict)).symm
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]

end Stacks.FlatComplexTopDegree
