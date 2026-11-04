module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The graded pieces `Iⁿ⁺¹M / Iⁿ⁺²M` of a flat module

Let `I` be an ideal of a ring `R` and let `r₁, …, r_d ∈ Iⁿ⁺¹` be elements whose images form a
basis of `Iⁿ⁺¹ / Iⁿ⁺²` over `R / I`, in the sense that they generate `Iⁿ⁺¹` modulo `Iⁿ⁺²` and that
`∑ aₖ rₖ ∈ Iⁿ⁺²` forces every `aₖ ∈ I`. For a flat `R`-module `M` the map
`(M / IM)ᵈ → Iⁿ⁺¹M / Iⁿ⁺²M`, `(xₖ) ↦ ∑ rₖ xₖ`, is then bijective. Surjectivity holds for every
module; injectivity is the equational criterion of flatness ([Stacks, Tag 00HK]).

The statements are made for a module `M` over an `R`-algebra `A`, flat over `R`, with the ideal
`I` extended to `A`: that is the form in which they are applied to the sections of a sheaf of
modules on a scheme over `Spec R`.

## Main results

* `Stacks.CubeOpenAtUnit.mem_smul_top_of_sum_smul_mem`: injectivity.
* `Stacks.CubeOpenAtUnit.exists_sub_sum_smul_mem`: surjectivity.

## References

* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

namespace Stacks.CubeOpenAtUnit

open Module

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) {d : ℕ} (r : Fin d → R)

section Base

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **Injectivity, over the base ring.** If `M` is flat and `∑ aₖ rₖ ∈ Iⁿ⁺²` forces `aₖ ∈ I`,
then `∑ rₖ xₖ ∈ Iⁿ⁺²M` forces `xₖ ∈ IM`. -/
theorem mem_smul_top_of_sum_smul_mem_base [Flat R M]
    (hind : ∀ a : Fin d → R, ∑ k, a k * r k ∈ I ^ (n + 2) → ∀ k, a k ∈ I)
    (x : Fin d → M) (hx : ∑ k, r k • x k ∈ I ^ (n + 2) • (⊤ : Submodule R M)) (k : Fin d) :
    x k ∈ I • (⊤ : Submodule R M) := by
  classical
  have hx' : ∑ k, r k • x k ∈ (I ^ (n + 2)) • Submodule.span R (Set.range (fun m : M => m)) := by
    rwa [Set.range_id', Submodule.span_univ]
  obtain ⟨c, hc, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum (I ^ (n + 2)) (fun m : M => m) _).1 hx'
  -- the relation `∑ rₖ xₖ - ∑ c(m) m = 0`, indexed by `Fin d ⊕ c.support`
  have hrel : ∑ i, Sum.elim r (fun m : c.support => -c m.1) i •
      Sum.elim x (fun m : c.support => m.1) i = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
    rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
    exact add_neg_cancel _
  obtain ⟨l, a, z, hy, hf⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hmem : ∀ j, a (Sum.inl k) j ∈ I := fun j => by
    have h := hf j
    rw [Fintype.sum_sum_type] at h
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h
    refine hind (fun k' => a (Sum.inl k') j) ?_ k
    have h' : ∑ k', r k' * a (Sum.inl k') j = ∑ m : c.support, c m.1 * a (Sum.inr m) j :=
      eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h)
    simp_rw [mul_comm (a _ j)]
    rw [h']
    exact Submodule.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hc m.1)
  rw [show x k = _ from hy (Sum.inl k)]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hmem j) Submodule.mem_top

/-- **Surjectivity, over the base ring.** If the `rₖ` generate `Iⁿ⁺¹` modulo `Iⁿ⁺²`, every
element of `Iⁿ⁺¹M` is `∑ rₖ xₖ` modulo `Iⁿ⁺²M`. -/
theorem exists_sub_sum_smul_mem_base
    (hspan : I ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ I ^ (n + 2))
    (y : M) (hy : y ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ x : Fin d → M, y - ∑ k, r k • x k ∈ I ^ (n + 2) • (⊤ : Submodule R M) := by
  classical
  let P : M → Prop := fun y => ∃ x : Fin d → M,
    y - ∑ k, r k • x k ∈ I ^ (n + 2) • (⊤ : Submodule R M)
  refine Submodule.smul_induction_on hy (p := P) (fun a ha m _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · obtain ⟨b, hb, t, ht, rfl⟩ := Submodule.mem_sup.1 (hspan ha)
    obtain ⟨g, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hb
    refine ⟨fun k => g k • m, ?_⟩
    have : (∑ k, g k * r k + t) • m - ∑ k, r k • g k • m = t • m := by
      rw [add_smul, Finset.sum_smul]
      simp_rw [smul_smul, mul_comm (r _)]
      abel
    rw [this]
    exact Submodule.smul_mem_smul ht Submodule.mem_top
  · obtain ⟨x₁, hx₁⟩ := h₁
    obtain ⟨x₂, hx₂⟩ := h₂
    refine ⟨x₁ + x₂, ?_⟩
    have : y₁ + y₂ - ∑ k, r k • (x₁ + x₂) k =
        (y₁ - ∑ k, r k • x₁ k) + (y₂ - ∑ k, r k • x₂ k) := by
      simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
      abel
    rw [this]
    exact Submodule.add_mem _ hx₁ hx₂

end Base

section Algebra

variable {A : Type*} [CommRing A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module A M]
  [Module R M] [IsScalarTower R A M]

/-- Restricting scalars from `A` to `R`, the submodule `(I A)ᵐM` is `IᵐM`. -/
theorem restrictScalars_pow_map_smul_top (m : ℕ) :
    ((I.map (algebraMap R A)) ^ m • (⊤ : Submodule A M)).restrictScalars R =
      I ^ m • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- Membership in `(I A)ᵐM` over `A` is membership in `IᵐM` over `R`. -/
private theorem mem_pow_map_smul_top_iff (m : ℕ) (x : M) :
    x ∈ (I.map (algebraMap R A)) ^ m • (⊤ : Submodule A M) ↔ x ∈ I ^ m • (⊤ : Submodule R M) := by
  rw [← restrictScalars_pow_map_smul_top I (A := A) m, Submodule.restrictScalars_mem]

/-- **Injectivity.** For `M` flat over `R`, `∑ rₖ xₖ ∈ (I A)ⁿ⁺²M` forces `xₖ ∈ (I A)M`. -/
theorem mem_smul_top_of_sum_smul_mem [Flat R M]
    (hind : ∀ a : Fin d → R, ∑ k, a k * r k ∈ I ^ (n + 2) → ∀ k, a k ∈ I)
    (x : Fin d → M)
    (hx : ∑ k, algebraMap R A (r k) • x k ∈
      (I.map (algebraMap R A)) ^ (n + 2) • (⊤ : Submodule A M)) (k : Fin d) :
    x k ∈ I.map (algebraMap R A) • (⊤ : Submodule A M) := by
  have h := mem_smul_top_of_sum_smul_mem_base I n r hind x
    ((mem_pow_map_smul_top_iff I (n + 2) _).1 (by simpa only [algebraMap_smul] using hx)) k
  simpa only [pow_one] using (mem_pow_map_smul_top_iff (A := A) I 1 _).2 (by rwa [pow_one])

/-- **Surjectivity.** If the `rₖ` generate `Iⁿ⁺¹` modulo `Iⁿ⁺²`, every element of `(I A)ⁿ⁺¹M` is
`∑ rₖ xₖ` modulo `(I A)ⁿ⁺²M`. -/
theorem exists_sub_sum_smul_mem
    (hspan : I ^ (n + 1) ≤ Ideal.span (Set.range r) ⊔ I ^ (n + 2))
    (y : M) (hy : y ∈ (I.map (algebraMap R A)) ^ (n + 1) • (⊤ : Submodule A M)) :
    ∃ x : Fin d → M, y - ∑ k, algebraMap R A (r k) • x k ∈
      (I.map (algebraMap R A)) ^ (n + 2) • (⊤ : Submodule A M) := by
  obtain ⟨x, hx⟩ := exists_sub_sum_smul_mem_base I n r hspan y
    ((mem_pow_map_smul_top_iff I (n + 1) _).1 hy)
  exact ⟨x, by simpa only [algebraMap_smul] using (mem_pow_map_smul_top_iff I (n + 2) _).2 hx⟩

end Algebra

end Stacks.CubeOpenAtUnit

end
