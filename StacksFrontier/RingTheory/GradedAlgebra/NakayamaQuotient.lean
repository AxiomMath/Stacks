module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Nakayama

/-!
# The graded Nakayama lemma modulo the irrelevant ideal

Let `A = ⨁ᵢ 𝒜ᵢ` be a graded ring with irrelevant ideal `𝒜₊ = ⨁_{i > 0} 𝒜ᵢ`, and let
`M = ⨁_d ℳ_d` be a finite graded `A`-module. This file gives the two assertions of the graded
Nakayama lemma that are read off modulo `𝒜₊M`:

* `LinearMap.surjective_of_surjective_mapQ_irrelevant_smul_top`: a map of graded modules `P → M`
  inducing a surjection `P/𝒜₊P → M/𝒜₊M` is surjective;
* `Submodule.span_range_eq_top_of_span_range_mkQ_irrelevant_eq_top`: homogeneous elements whose
  images generate `M/𝒜₊M` generate `M`.

## Implementation notes

Both are proved from `Submodule.IsHomogeneous.eq_top_of_sup_irrelevant_smul_eq_top`, applied to
the range of the map, homogeneous by `LinearMap.isHomogeneous_range`, respectively to the span of
the elements, homogeneous by `Submodule.isHomogeneous_span`, with `N' = ⊤`. Since they involve
quotient modules they are stated over a commutative ring and additive groups, as in the source. In
the first, the hypothesis is the surjectivity of `Submodule.mapQ`, the map `P/𝒜₊P → M/𝒜₊M` induced
by `f`; in the second, the elements are a family `x : Fin n → M` whose images under the quotient
map `M → M/𝒜₊M` span the quotient.

## References

* [StacksProject 0EKB](https://stacks.math.columbia.edu/tag/0EKB)
-/

open scoped HomogeneousIdeal

@[expose] public section

variable {ιA ιM σA σM A M : Type*}
  [DecidableEq ιA] [AddCommMonoid ιA] [PartialOrder ιA] [CanonicallyOrderedAdd ιA]
  [DecidableEq ιM] [PartialOrder ιM] [AddAction ιA ιM] [IsOrderedCancelVAdd ιA ιM]

/-- **Stacks 0EKB (3)**. Let `A = ⨁ᵢ 𝒜ᵢ` be a graded ring, and let `f : P → M` be a map of graded
`A`-modules, i.e. a linear map sending `𝒩 d` into `ℳ d` for every degree `d`. If the induced map
`P/𝒜₊P → M/𝒜₊M` is surjective and `M` is finite, then `f` is surjective. -/
@[stacks 0EKB "(3)"]
public theorem LinearMap.surjective_of_surjective_mapQ_irrelevant_smul_top {σP P : Type*}
    [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    [SetLike σA A] [AddSubmonoidClass σA A] {𝒜 : ιA → σA} [GradedRing 𝒜]
    [SetLike σM M] [AddSubmonoidClass σM M] {ℳ : ιM → σM} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ]
    [SetLike σP P] [AddSubmonoidClass σP P] {𝒩 : ιM → σP} [DirectSum.Decomposition 𝒩]
    [Module.Finite A M] (f : P →ₗ[A] M) (hf : ∀ i, ∀ x ∈ 𝒩 i, f x ∈ ℳ i)
    (h : Function.Surjective ((𝒜₊.toIdeal • ⊤ : Submodule A P).mapQ
      (𝒜₊.toIdeal • ⊤ : Submodule A M) f (Submodule.smul_top_le_comap_smul_top _ f))) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  have hrange := LinearMap.range_eq_top.mpr h
  rw [Submodule.range_mapQ] at hrange
  refine (f.isHomogeneous_range hf).eq_top_of_sup_irrelevant_smul_eq_top (𝒜 := 𝒜) (N' := ⊤)
    (fun _ _ _ => Submodule.mem_top) Module.Finite.fg_top ?_
  rw [sup_comm, ← Submodule.comap_map_mkQ, hrange, Submodule.comap_top]

/-- **Stacks 0EKB (4)**. Let `A = ⨁ᵢ 𝒜ᵢ` be a graded ring and `M = ⨁_d ℳ_d` a finite graded
`A`-module. If `x₁, …, xₙ ∈ M` are homogeneous and their images generate `M/𝒜₊M`, then
`x₁, …, xₙ` generate `M`. -/
@[stacks 0EKB "(4)"]
public theorem Submodule.span_range_eq_top_of_span_range_mkQ_irrelevant_eq_top
    [CommRing A] [AddCommGroup M] [Module A M]
    [SetLike σA A] [AddSubmonoidClass σA A] {𝒜 : ιA → σA} [GradedRing 𝒜]
    [SetLike σM M] [AddSubmonoidClass σM M] {ℳ : ιM → σM} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite A M] {n : ℕ} {x : Fin n → M}
    (hx : ∀ k, ∃ i, x k ∈ ℳ i)
    (h : Submodule.span A (Set.range ((𝒜₊.toIdeal • ⊤ : Submodule A M).mkQ ∘ x)) = ⊤) :
    Submodule.span A (Set.range x) = ⊤ := by
  refine (Submodule.isHomogeneous_span (𝒜 := 𝒜) (ℳ := ℳ) ?_).eq_top_of_sup_irrelevant_smul_eq_top
    (𝒜 := 𝒜) (N' := ⊤) (fun _ _ _ => Submodule.mem_top) Module.Finite.fg_top ?_
  · rintro _ ⟨k, rfl⟩
    exact hx k
  · rw [Set.range_comp, ← Submodule.map_span] at h
    rw [sup_comm, ← Submodule.comap_map_mkQ, h, Submodule.comap_top]

end
