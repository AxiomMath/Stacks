module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Membership in a submodule descends along a finite faithfully flat product

Let `A → ∏ᵢ Bᵢ` be faithfully flat with `ι` finite, and let `rᵢ : M → Mᵢ` be `A`-linear maps into
`Bᵢ`-modules whose base changes `Bᵢ ⊗_A M → Mᵢ` are bijective.  For a submodule `N ⊆ M`, an
element `x ∈ M` lies in `N` as soon as each `rᵢ x` lies in the `Bᵢ`-span of `rᵢ(N)`.

The proof passes to the quotient `M ⧸ N`: the hypothesis says that `1 ⊗ x̄` vanishes in every
`Bᵢ ⊗_A (M ⧸ N)`, hence in `(∏ᵢ Bᵢ) ⊗_A (M ⧸ N)`, and faithful flatness makes
`M ⧸ N → (∏ᵢ Bᵢ) ⊗_A (M ⧸ N)` injective.

This is the algebra behind the statement that membership of a section of a quasi-coherent module
in the span of the restriction of a submodule is local for the fppf topology (faithfully flat
descent, Stacks 023M).

## Main results

* `Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange_pi`

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open TensorProduct

/-- **Membership in a submodule descends along a finite faithfully flat product.**  If
`A → ∏ᵢ Bᵢ` is faithfully flat, `ι` finite, and `rᵢ : M → Mᵢ` are `A`-linear maps whose base
changes `Bᵢ ⊗_A M → Mᵢ` are bijective, then `x ∈ N` as soon as every `rᵢ x` lies in the
`Bᵢ`-span of `rᵢ(N)`. -/
theorem Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange_pi
    {ι : Type*} [Finite ι] (A : Type*) [CommRing A] (Bi : ι → Type*) [∀ i, CommRing (Bi i)]
    [∀ i, Algebra A (Bi i)] [Module.FaithfullyFlat A (∀ i, Bi i)]
    {M : Type*} [AddCommGroup M] [Module A M] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)]
    [∀ i, Module (Bi i) (Mi i)] [∀ i, Module A (Mi i)] [∀ i, IsScalarTower A (Bi i) (Mi i)]
    (r : ∀ i, M →ₗ[A] Mi i) (hr : ∀ i, Function.Bijective ((r i).liftBaseChange (Bi i)))
    (N : Submodule A M) {x : M} (hx : ∀ i, r i x ∈ Submodule.span (Bi i) (r i '' N)) :
    x ∈ N := by
  classical
  have := Fintype.ofFinite ι
  rw [← Submodule.Quotient.mk_eq_zero]
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := ∀ i, Bi i)
  rw [map_zero]
  apply (TensorProduct.piLeft A (M ⧸ N) Bi).injective
  rw [map_zero]
  funext i
  have hpi : TensorProduct.piLeft A (M ⧸ N) Bi ((1 : ∀ i, Bi i) ⊗ₜ[A] (Submodule.Quotient.mk x))
      i = (1 : Bi i) ⊗ₜ[A] Submodule.Quotient.mk x := by
    simp [TensorProduct.piLeft]
  rw [TensorProduct.mk_apply, hpi, Pi.zero_apply]
  have hspan : Submodule.span (Bi i) (r i '' N) ≤
      (Submodule.span (Bi i) ((fun n => (1 : Bi i) ⊗ₜ[A] n) '' N)).map
        ((r i).liftBaseChange (Bi i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨1 ⊗ₜ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩
  obtain ⟨y, hy, hye⟩ := hspan (hx i)
  obtain rfl : (1 : Bi i) ⊗ₜ[A] x = y := (hr i).1 (by rw [hye]; simp)
  let π := (N.mkQ).baseChange (Bi i)
  have h0 : π ((1 : Bi i) ⊗ₜ[A] x) = 0 := by
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by simp [ha, hb])
      (fun _ _ _ ha ↦ by simp [ha]) hy
    rintro _ ⟨n, hn, rfl⟩
    simp [π, (Submodule.Quotient.mk_eq_zero N).2 hn]
  simpa [π] using h0

end
