module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Ideal.Span

/-!
# Koszul syzygies of a family generating the unit ideal

Let `R` be a commutative ring and `a : I → R` a family generating `R` as an `R`-module, with `I`
an arbitrary index type. The *Koszul syzygies* of `a` are the elements
`a j • single i 1 - a i • single j 1` of `I →₀ R`; they are relations among the `a i`, and this
file proves that they are all of them: they span the kernel of
`Finsupp.linearCombination R a : (I →₀ R) →ₗ[R] R`.

The geometric form of the same statement is also proved here: if `A` is free with basis `b`
indexed by `I`, `M` is free of rank one, and `π : A →ₗ[R] M` carries `b i` to a family spanning
`M`, then the kernel of `π ⊗ 1_M : A ⊗ M → M ⊗ M` is spanned by the elements
`b i ⊗ π (b j) - b j ⊗ π (b i)`. This is what a sheaf-theoretic argument meets at a stalk.

## Main results

* `Koszul.span_koszul_eq_ker_linearCombination`: **the Koszul syzygies of a unit-ideal family
  span the syzygy module.**
* `Koszul.mem_span_koszul_of_linearCombination_eq_zero`: the membership form of the same
  statement.
* `Koszul.span_koszul_tmul_eq_ker_map_id`: **the Koszul relations span the kernel of `π ⊗ 1`**
  for a rank-one target.

## Implementation notes

`StacksFrontier.RingTheory.Koszul.Relations` carries the counterpart of the first result for a
sequence indexed by `Fin r`: there the syzygies are `Koszul.trivRel` and the submodule they span
is `Koszul.relSpan`, and `Koszul.isZero_homology_seqComplex_of_span_eq_top` of
`StacksFrontier.RingTheory.Koszul.PowerLift.UnitEntry` gives the vanishing of every Koszul homology
of a unit-ideal sequence, hence `Koszul.relSpan f = LinearMap.ker (Koszul.seqDual f)`. Neither
serves here, because both are stated for a finite sequence in a fixed `Fin r` and the index type
of a generating family of global sections of a sheaf of modules is arbitrary. The proof below is
elementary and independent of the exterior-algebra machinery those results use.

The proof of the second result is the first one transported along the two identifications
`A ⊗ M ≅ (I →₀ R)` and `M ⊗ M ≅ R` induced by the basis and the rank-one witness.
-/

@[expose] public section

open scoped TensorProduct

namespace Koszul

/-! ### Syzygies of a family generating the unit ideal -/

section Syzygies

variable {R : Type*} [CommRing R] {I : Type*}

/-- Every Koszul syzygy of `a` lies in the kernel of `x ↦ ∑ i, x i * a i`. -/
theorem span_koszul_le_ker_linearCombination (a : I → R) :
    Submodule.span R
        (Set.range fun p : I × I ↦
          a p.2 • Finsupp.single p.1 (1 : R) - a p.1 • Finsupp.single p.2 (1 : R)) ≤
      LinearMap.ker (Finsupp.linearCombination R a) := by
  rw [Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  simp [SetLike.mem_coe, LinearMap.mem_ker, mul_comm]

/-- If `a : I → R` generates the unit ideal, every syzygy of `a` is an `R`-linear combination of
the Koszul syzygies `a j • single i 1 - a i • single j 1`. -/
theorem mem_span_koszul_of_linearCombination_eq_zero (a : I → R)
    (ha : Submodule.span R (Set.range a) = ⊤) (x : I →₀ R)
    (hx : Finsupp.linearCombination R a x = 0) :
    x ∈ Submodule.span R
      (Set.range fun p : I × I ↦
        a p.2 • Finsupp.single p.1 (1 : R) - a p.1 • Finsupp.single p.2 (1 : R)) := by
  obtain ⟨c, hc⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.1 (ha ▸ Submodule.mem_top : (1 : R) ∈ _)
  have hc' : ∑ k ∈ c.support, c k * a k = 1 := by
    simpa [Finsupp.sum, smul_eq_mul] using hc
  have hx' : ∑ j ∈ x.support, x j * a j = 0 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] using hx
  have hxs : ∑ j ∈ x.support, Finsupp.single j (x j) = x := by
    simpa [Finsupp.sum] using Finsupp.sum_single x
  have hk : ∀ k : I, a k • x ∈ Submodule.span R
      (Set.range fun p : I × I ↦
        a p.2 • Finsupp.single p.1 (1 : R) - a p.1 • Finsupp.single p.2 (1 : R)) := by
    intro k
    have hzero : ∑ j ∈ x.support, Finsupp.single k (x j * a j) = 0 := by
      rw [← Finsupp.single_finsetSum, hx', Finsupp.single_zero]
    have key : a k • x = ∑ j ∈ x.support,
        x j • (a k • Finsupp.single j (1 : R) - a j • Finsupp.single k (1 : R)) := by
      simp only [smul_sub, Finset.sum_sub_distrib, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hzero, sub_zero]
      conv_lhs => rw [← hxs]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Finsupp.smul_single, smul_eq_mul, mul_comm]
    rw [key]
    exact Submodule.sum_smul_mem _ _ fun j _ => Submodule.subset_span ⟨(j, k), rfl⟩
  have hxsum : x = ∑ k ∈ c.support, c k • (a k • x) := by
    conv_lhs => rw [← one_smul R x, ← hc']
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_smul]
  rw [hxsum]
  exact Submodule.sum_smul_mem _ _ fun k _ => hk k

/-- **The Koszul syzygies of a unit-ideal family span the syzygy module.** -/
theorem span_koszul_eq_ker_linearCombination (a : I → R)
    (ha : Submodule.span R (Set.range a) = ⊤) :
    Submodule.span R
        (Set.range fun p : I × I ↦
          a p.2 • Finsupp.single p.1 (1 : R) - a p.1 • Finsupp.single p.2 (1 : R)) =
      LinearMap.ker (Finsupp.linearCombination R a) :=
  le_antisymm (span_koszul_le_ker_linearCombination a) fun x hx =>
    mem_span_koszul_of_linearCombination_eq_zero a ha x hx

end Syzygies

/-! ### Rank-one targets -/

section RankOne

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A family in a module that is free of rank one spans it if and only if the family of
corresponding scalars spans the base ring. -/
private theorem span_eq_top_iff_span_linearEquiv_eq_top (e : M ≃ₗ[R] R) {I : Type*} (s : I → M) :
    Submodule.span R (Set.range s) = ⊤ ↔ Submodule.span R (Set.range (fun i ↦ e (s i))) = ⊤ := by
  have key : Submodule.map (e : M →ₗ[R] R) (Submodule.span R (Set.range s))
      = Submodule.span R (Set.range (fun i ↦ e (s i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← key]
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  refine Submodule.map_injective_of_injective (f := (e : M →ₗ[R] R)) e.injective ?_
  rw [h, Submodule.map_top]
  simp

end RankOne

/-! ### The Koszul relations span the kernel of a tensored map -/

section TensorKernel

variable {R : Type*} [CommRing R] {ι : Type*} {A M : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]

/-- **The Koszul relations span the kernel of `π ⊗ 1`.** Let `A` be free with basis `b` indexed
by `ι`, let `M` be free of rank one, witnessed by `e : M ≃ₗ[R] R`, and let `π : A →ₗ[R] M` carry
`b i` to `sgen i`, where the family `sgen` spans `M`. Then the kernel of
`π ⊗ 1_M : A ⊗ M → M ⊗ M` is spanned by the elements `b i ⊗ sgen j - b j ⊗ sgen i`. -/
theorem span_koszul_tmul_eq_ker_map_id (b : Module.Basis ι R A) (e : M ≃ₗ[R] R)
    (π : A →ₗ[R] M) (sgen : ι → M) (hπ : ∀ i, π (b i) = sgen i)
    (hspan : Submodule.span R (Set.range sgen) = ⊤) :
    Submodule.span R
        (Set.range fun p : ι × ι ↦ b p.1 ⊗ₜ[R] sgen p.2 - b p.2 ⊗ₜ[R] sgen p.1)
      = LinearMap.ker (TensorProduct.map π (LinearMap.id : M →ₗ[R] M)) := by
  classical
  set c : ι → R := fun i => e (sgen i) with hc
  set Φ : A ⊗[R] M ≃ₗ[R] (ι →₀ R) :=
    (TensorProduct.congr b.repr e).trans (TensorProduct.rid R (ι →₀ R)) with hΦ
  set Ψ : M ⊗[R] M ≃ₗ[R] R :=
    (TensorProduct.congr e e).trans (TensorProduct.rid R R) with hΨ
  have hΦ_tmul : ∀ (a : A) (m : M), Φ (a ⊗ₜ[R] m) = e m • b.repr a := by
    intro a m; simp [hΦ]
  have hΨ_tmul : ∀ (m n : M), Ψ (m ⊗ₜ[R] n) = e n * e m := by
    intro m n; simp [hΨ, mul_comm]
  have h1 : (e : M →ₗ[R] R) ∘ₗ π = (Finsupp.linearCombination R c) ∘ₗ b.repr.toLinearMap := by
    refine b.ext fun i => ?_
    simp [hπ i, hc]
  have h2 : (Ψ : M ⊗[R] M →ₗ[R] R) ∘ₗ (TensorProduct.map π (LinearMap.id : M →ₗ[R] M))
      = (Finsupp.linearCombination R c) ∘ₗ (Φ : A ⊗[R] M →ₗ[R] (ι →₀ R)) := by
    refine TensorProduct.ext' fun a m => ?_
    have h1a : e (π a) = Finsupp.linearCombination R c (b.repr a) :=
      congrArg (fun f : A →ₗ[R] R => f a) h1
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      LinearEquiv.coe_coe, hΨ_tmul, hΦ_tmul, map_smul, smul_eq_mul, h1a]
  have hker : LinearMap.ker (TensorProduct.map π (LinearMap.id : M →ₗ[R] M))
      = Submodule.comap (Φ : A ⊗[R] M →ₗ[R] (ι →₀ R))
          (LinearMap.ker (Finsupp.linearCombination R c)) := by
    ext z
    have hz := LinearMap.congr_fun h2 z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
    simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [← hz, LinearEquiv.map_eq_zero_iff]
  have hspanc : Submodule.span R (Set.range c) = ⊤ :=
    (span_eq_top_iff_span_linearEquiv_eq_top e sgen).mp hspan
  have himg : ∀ p : ι × ι, Φ (b p.1 ⊗ₜ[R] sgen p.2 - b p.2 ⊗ₜ[R] sgen p.1)
      = c p.2 • Finsupp.single p.1 (1 : R) - c p.1 • Finsupp.single p.2 (1 : R) := by
    intro p
    rw [map_sub, hΦ_tmul, hΦ_tmul, b.repr_self, b.repr_self]
  rw [hker, Submodule.comap_equiv_eq_map_symm, ← span_koszul_eq_ker_linearCombination c hspanc,
    Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  refine congrArg Set.range (funext fun p => ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_coe]
  exact (Φ.symm_apply_eq.2 (himg p).symm).symm

end TensorKernel

end Koszul
