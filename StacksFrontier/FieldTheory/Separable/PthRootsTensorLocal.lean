module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.FieldTheory.Separable.TFAE

@[expose] public section

/-!
# The tensor product of a field extension with the `p`-th roots of the base

Let `k` be a field of exponential characteristic `p` and let `K/k` be a field extension. The
ring `T = K ⊗[k] k^{1/p}` is *local with nilpotent maximal ideal*: every one of its elements is
either a unit or nilpotent, because the `p`-th power of `x ⊗ a` is `(a^p x^p) ⊗ 1` and `a ^ p`
lies in `k`, so the `p`-th power of any element of `T` lies in the image of the field `K`.

Reducedness of `T` is one of the four equivalent forms of separability of `K/k`
(`Algebra.isSeparableExtension_tfae`, Stacks Tag 030W), and the locality above turns that into a
criterion testable at a single point of a base change: if *some* nonzero reduced ring is a flat
`T`-algebra, then `T` is reduced, hence `K/k` is separable. Indeed the maximal ideal of `T`
consists of nilpotents, so it acts as zero on a reduced algebra; a flat algebra on which the
maximal ideal acts as zero without being zero itself is faithfully flat, hence injective on `T`.

## Main results

* `Algebra.isUnit_or_isNilpotent_tensorAdjoinPthRoots` — every element of `K ⊗[k] k^{1/p}` is a
  unit or nilpotent.
* `Algebra.isSeparableExtension_of_flat_isReduced` — a field extension with a nonzero reduced
  flat algebra over `K ⊗[k] k^{1/p}` is separable.

## References

* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

open scoped TensorProduct

namespace Algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (p : ℕ) [ExpChar k p]

/-- The `p`-th power of an element of `K ⊗[k] k^{1/p}` lies in the image of `K`: the `p`-th power
of `a` is `algebraMap k (AdjoinPthRoots k) a'` for a unique `a' : k`, and raising to the `p`-th
power is additive. -/
theorem exists_tmul_one_eq_pow_expChar_tensorAdjoinPthRoots
    (t : K ⊗[k] AdjoinPthRoots k) : ∃ y : K, t ^ p = y ⊗ₜ[k] (1 : AdjoinPthRoots k) := by
  have hT : ExpChar (K ⊗[k] AdjoinPthRoots k) p :=
    expChar_of_injective_algebraMap (algebraMap k _).injective p
  have hp : p ≠ 0 := (expChar_pos k p).ne'
  induction t with
  | zero => exact ⟨0, by simp [zero_pow hp]⟩
  | tmul x a =>
      refine ⟨(AdjoinPthRoots.root k).symm a • x ^ p, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, AdjoinPthRoots.algebraMap_root_symm (p := p) a |>.symm,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add u v hu hv =>
      obtain ⟨yu, hyu⟩ := hu
      obtain ⟨yv, hyv⟩ := hv
      exact ⟨yu + yv, by rw [add_pow_expChar, hyu, hyv, TensorProduct.add_tmul]⟩

/-- **Every element of `K ⊗[k] k^{1/p}` is a unit or nilpotent.** Its `p`-th power is `y ⊗ 1`
for some `y : K`, and that is a unit when `y ≠ 0` and zero otherwise. -/
theorem isUnit_or_isNilpotent_tensorAdjoinPthRoots (t : K ⊗[k] AdjoinPthRoots k) :
    IsUnit t ∨ IsNilpotent t := by
  obtain ⟨y, hy⟩ :=
    exists_tmul_one_eq_pow_expChar_tensorAdjoinPthRoots k K (ringExpChar k) t
  rcases eq_or_ne y 0 with rfl | hne
  · exact Or.inr ⟨ringExpChar k, by rw [hy, TensorProduct.zero_tmul]⟩
  · refine Or.inl ((isUnit_pow_iff (expChar_pos k (ringExpChar k)).ne').mp ?_)
    refine hy ▸ IsUnit.of_mul_eq_one (y⁻¹ ⊗ₜ[k] (1 : AdjoinPthRoots k)) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hne, mul_one,
      Algebra.TensorProduct.one_def]

/-- `K ⊗[k] k^{1/p}` is a local ring: its non-units are its nilpotent elements, and those form
an ideal. -/
instance isLocalRing_tensorAdjoinPthRoots :
    IsLocalRing (K ⊗[k] AdjoinPthRoots k) := by
  have hnil : ∀ t : K ⊗[k] AdjoinPthRoots k, t ∈ nonunits _ → IsNilpotent t := by
    intro t ht
    exact (isUnit_or_isNilpotent_tensorAdjoinPthRoots k K t).resolve_left ht
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  exact ((Commute.all a b).isNilpotent_add (hnil a ha) (hnil b hb)).not_isUnit

/-- Every element of the maximal ideal of `K ⊗[k] k^{1/p}` is nilpotent. -/
theorem isNilpotent_of_mem_maximalIdeal_tensorAdjoinPthRoots
    {t : K ⊗[k] AdjoinPthRoots k} (ht : t ∈ IsLocalRing.maximalIdeal _) : IsNilpotent t :=
  (isUnit_or_isNilpotent_tensorAdjoinPthRoots k K t).resolve_left
    ((IsLocalRing.mem_maximalIdeal _).mp ht)

/-- **A field extension with a nonzero reduced flat algebra over `K ⊗[k] k^{1/p}` is
separable.**

The maximal ideal of `T = K ⊗[k] k^{1/p}` consists of nilpotents, hence acts as zero on the
reduced algebra `S`; as `S` is nonzero and flat it is therefore faithfully flat over `T`, so
`T → S` is injective and `T` is reduced. Reducedness of `T` is separability of `K/k` by Stacks
Tag 030W. -/
theorem isSeparableExtension_of_flat_isReduced (S : Type*) [CommRing S] [Nontrivial S]
    [IsReduced S] [Algebra (K ⊗[k] AdjoinPthRoots k) S]
    [Module.Flat (K ⊗[k] AdjoinPthRoots k) S] :
    Algebra.IsSeparableExtension k K := by
  have hzero : ∀ t ∈ IsLocalRing.maximalIdeal (K ⊗[k] AdjoinPthRoots k),
      algebraMap (K ⊗[k] AdjoinPthRoots k) S t = 0 :=
    fun t ht => (isNilpotent_of_mem_maximalIdeal_tensorAdjoinPthRoots k K ht).map
      (algebraMap _ S) |>.eq_zero
  have hsmul : (IsLocalRing.maximalIdeal (K ⊗[k] AdjoinPthRoots k)) •
      (⊤ : Submodule (K ⊗[k] AdjoinPthRoots k) S) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun t ht s _ => ?_) bot_le
    simp [Algebra.smul_def, hzero t ht]
  have htop : (⊥ : Submodule (K ⊗[k] AdjoinPthRoots k) S) ≠ ⊤ := by
    intro h
    have : (1 : S) ∈ (⊥ : Submodule (K ⊗[k] AdjoinPthRoots k) S) := h ▸ Submodule.mem_top
    exact one_ne_zero (Submodule.mem_bot _ |>.mp this)
  have : Module.FaithfullyFlat (K ⊗[k] AdjoinPthRoots k) S := by
    refine ⟨fun {m} hm => ?_⟩
    rw [IsLocalRing.eq_maximalIdeal hm, hsmul]
    exact htop
  have hred : IsReduced (K ⊗[k] AdjoinPthRoots k) :=
    isReduced_of_injective (algebraMap (K ⊗[k] AdjoinPthRoots k) S)
      (FaithfulSMul.algebraMap_injective _ S)
  exact ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 3 1).mp hred

end Algebra

end
