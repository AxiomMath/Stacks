module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExact

/-!
# The equalizer sequence over a discrete valuation ring

Let `V` be a discrete valuation ring with residue field `k`, and let `p₁ p₂ : C → D` be two maps
of flat `V`-algebras. Suppose that the equalizer `Γ = ker(p₁ - p₂) ⊆ C` is a finite `V`-module
and that the equalizer sequence `0 → k → k ⊗_V C → k ⊗_V D` of `AlgHom.EqualizerTensorExact`
is exact. Then the sequence `0 → V → C → D` is exact, that is `Γ = V`; by flat base change
(`AlgHom.EqualizerTensorExact.of_flat`) it is then exact after tensoring with every flat
`V`-module, for instance the fraction field of `V` or an algebraic closure of it.

For the chart algebras `C = Γ(U, 𝒪)` and `D = Γ(U ×_X U, 𝒪)` of an algebraic space `X` proper
and flat over `Spec V`, this says: if the closed fibre has only constant global functions,
`H⁰(X_k, 𝒪) = k`, then so does every flat base change of `X`, in particular the generic fibre
and its base changes to extensions of the fraction field. Finiteness of `Γ = H⁰(X, 𝒪)` is
Stacks 08AS.

## Main results

* `AlgHom.EqualizerTensorExact.self_of_residueField_of_isDiscreteValuationRing`: the statement
  above.

## Implementation notes

The proof is Nakayama's lemma. Let `π` be a uniformizer. For `c ∈ Γ` exactness over `k` writes
`1 ⊗ c` as `λ̄ ⊗ 1`, so `c - λ ∈ π C`; writing `c - λ = π c'`, the element `c'` lies again in `Γ`
because `D` is torsion free. So `Γ ⊆ V · 1 + π Γ`, and `Γ = V · 1` since `Γ` is finite.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace AlgHom

variable {V C D : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [CommRing C] [CommRing D] [Algebra V C] [Algebra V D] [Module.Flat V C] [Module.Flat V D]
  {p₁ p₂ : C →ₐ[V] D}

omit [Module.Flat V C] in
/-- An element of `C` which vanishes in `k ⊗_V C` is a multiple of the uniformizer. -/
private theorem exists_smul_eq_of_tmul_eq_zero {ϖ : V} (hϖ : Irreducible ϖ) {y : C}
    (hy : (1 : V ⧸ maximalIdeal V) ⊗ₜ[V] y = 0) : ∃ y' : C, ϖ • y' = y := by
  have h := congrArg (TensorProduct.quotTensorEquivQuotSMul C (maximalIdeal V)) hy
  rw [← map_one (Ideal.Quotient.mk (maximalIdeal V)), TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    one_smul, map_zero,
    Submodule.Quotient.mk_eq_zero, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨y', -, hy'⟩ := h
  exact ⟨y', hy'⟩

omit [IsDiscreteValuationRing V] in
/-- Multiplication by a nonzero element of `V` is injective on a flat `V`-algebra. -/
private theorem smul_injective_of_flat {E : Type*} [CommRing E] [Algebra V E] [Module.Flat V E]
    {a : V} (ha : a ≠ 0) : Function.Injective (fun e : E => a • e) := fun e₁ e₂ he =>
  (IsSMulRegular.of_ne_zero ha).of_flat (S := E) (by simpa only [algebraMap_smul] using he)

/-- **The equalizer sequence over a discrete valuation ring.** Let `V` be a discrete valuation
ring with residue field `k` and let `p₁ p₂ : C → D` be two maps of flat `V`-algebras whose
equalizer `ker(p₁ - p₂)` is a finitely generated `V`-submodule of `C`. If the sequence
`0 → k → k ⊗_V C → k ⊗_V D` is exact, then so is `0 → V → C → D`. -/
theorem EqualizerTensorExact.self_of_residueField_of_isDiscreteValuationRing
    (hfin : (LinearMap.ker (p₁.toLinearMap - p₂.toLinearMap)).FG)
    (h : EqualizerTensorExact p₁ p₂ (V ⧸ maximalIdeal V)) : EqualizerTensorExact p₁ p₂ V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  rw [equalizerTensorExact_iff_tmulOne] at h ⊢
  obtain ⟨hinjk, hexk⟩ := h
  set K := LinearMap.ker (p₁.toLinearMap - p₂.toLinearMap)
  set N := LinearMap.range (Algebra.linearMap V C)
  -- `K ⊆ V · 1 + ϖ K`
  have hstep : K ≤ N ⊔ maximalIdeal V • K := by
    intro c hc
    have hc' : (p₁.toLinearMap - p₂.toLinearMap) c = 0 := hc
    obtain ⟨n, hn⟩ := hexk ((1 : V ⧸ maximalIdeal V) ⊗ₜ[V] c) (by
      rw [LinearMap.lTensor_tmul, hc', TensorProduct.tmul_zero])
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective n
    have hl : (1 : V ⧸ maximalIdeal V) ⊗ₜ[V] (c - algebraMap V C l) = 0 := by
      rw [TensorProduct.tmul_sub, ← hn, tmulOne_apply, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', sub_eq_zero, Algebra.smul_def,
        mul_one]
      rfl
    obtain ⟨y', hy'⟩ := exists_smul_eq_of_tmul_eq_zero hϖ hl
    have hy'K : y' ∈ K := by
      show (p₁.toLinearMap - p₂.toLinearMap) y' = 0
      apply smul_injective_of_flat (E := D) hϖ0
      show ϖ • (p₁.toLinearMap - p₂.toLinearMap) y' = ϖ • 0
      rw [← LinearMap.map_smul, hy', map_sub, hc', smul_zero, zero_sub, neg_eq_zero]
      show p₁ (algebraMap V C l) - p₂ (algebraMap V C l) = 0
      rw [AlgHom.commutes, AlgHom.commutes, sub_self]
    have hc_eq : c = algebraMap V C l + ϖ • y' := by rw [hy', add_sub_cancel]
    rw [hc_eq]
    refine Submodule.add_mem_sup ⟨l, rfl⟩ ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) hy'K
  have hKN : K ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfin (maximalIdeal_le_jacobson _) hstep
  refine ⟨?_, fun x hx => ?_⟩
  · -- injectivity of `n ↦ n ⊗ 1`
    intro a b hab
    by_contra hne
    have hsub : (a - b) ⊗ₜ[V] (1 : C) = 0 := by
      rw [TensorProduct.sub_tmul]
      exact sub_eq_zero.mpr hab
    have h1 : (a - b) • (1 : C) = 0 := by
      have := congrArg (TensorProduct.lid V C) hsub
      rwa [TensorProduct.lid_tmul, map_zero] at this
    have hC : (1 : C) = 0 := smul_injective_of_flat (E := C) (sub_ne_zero.mpr hne)
      (h1.trans (smul_zero _).symm)
    have hk : (1 : V ⧸ maximalIdeal V) = 0 := by
      apply hinjk
      rw [tmulOne_apply, tmulOne_apply, hC, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
    exact one_ne_zero hk
  · -- exactness in the middle
    set c := TensorProduct.lid V C x with hcdef
    have hx' : x = (1 : V) ⊗ₜ[V] c := by
      rw [hcdef, ← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
    have hcK : c ∈ K := by
      rw [hx', LinearMap.lTensor_tmul] at hx
      have := congrArg (TensorProduct.lid V D) hx
      rwa [TensorProduct.lid_tmul, one_smul, map_zero] at this
    obtain ⟨l, hl⟩ := hKN hcK
    refine ⟨l, ?_⟩
    rw [tmulOne_apply, hx', ← hl, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

end AlgHom
