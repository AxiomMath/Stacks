module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Support.Basic

/-!
# The annihilator of the cokernel of a section, under base change

Let `B` be a commutative ring, `M` a `B`-module and `τ : M`. The ideal
`Ann_B(M / Bτ)` is the annihilator of the cokernel of the map `B → M`, `b ↦ b τ`. This file
records how that ideal behaves under a base change `B → B₁`: it always extends into the
corresponding ideal of `B₁ ⊗_B M` with section `1 ⊗ τ`, the two agree up to radical, and they
agree on the nose if `B → B₁` is flat or if `M` is an invertible `B`-module.

This is the commutative-algebra content of [Stacks, Tag 0BW7]: the different of a flat
quasi-finite morphism is, on an affine chart, exactly such an ideal for the relative dualizing
module and its trace element.

## Main definitions

* `Stacks.Annihilator.cokerSpanIdeal`: the ideal `Ann_B(M / Bτ)`.
* `Stacks.Annihilator.baseChangeQuotEquiv`: the identification
  `(B₁ ⊗_B M) / B₁(1 ⊗ τ) ≃ B₁ ⊗_B (M / Bτ)`, i.e. right exactness of base change applied to
  the cokernel of `τ`.

## Main results

* `Stacks.Annihilator.map_cokerSpanIdeal_le`: the extension of `Ann_B(M / Bτ)` to `B₁` is
  contained in `Ann_{B₁}((B₁ ⊗_B M) / B₁(1 ⊗ τ))`.
* `Stacks.Annihilator.zeroLocus_cokerSpanIdeal_tmul`: for finite `M` the two ideals cut out the
  same closed subset of `Spec B₁`, namely the inverse image of the closed subset cut out by
  `Ann_B(M / Bτ)`.
* `Stacks.Annihilator.map_cokerSpanIdeal_eq_of_flat`: for flat `B → B₁` and finite `M` the
  inclusion is an equality.
* `Stacks.Annihilator.cokerSpanIdeal_tmul_le_map_range_eval`: for invertible `M` the ideal over
  `B₁` is contained in the extension of the image of evaluation at `τ` on the dual of `M`.

## Implementation notes

The base change is written `B₁ ⊗[B] M`, with the new ring on the left, which is Mathlib's
orientation and the one for which the `B₁`-module structure is found by instance search.

`Stacks.Annihilator.baseChangeQuotEquiv` is built by hand from the universal properties of the
two quotients rather than from a right-exactness lemma, because the equivalence is needed as a
`B₁`-linear map and Mathlib's `TensorProduct.tensorQuotientEquiv` is only linear over the base
ring `B`.

The invertible case is stated as an inclusion into the extension of the image of evaluation at
`τ`; that image is the ideal `Ann_B(M / Bτ)` itself, but the proof of that is
`Stacks.Discriminant.range_eval_eq_annihilator_quotient_span`, which lives further downstream,
so the two halves are combined there.

## References

* [Stacks Project, Tag 0BW7](https://stacks.math.columbia.edu/tag/0BW7)
* [Stacks Project, Tag 07T8](https://stacks.math.columbia.edu/tag/07T8)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
* [Stacks Project, Tag 00L2](https://stacks.math.columbia.edu/tag/00L2)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Annihilator

variable {M : Type*}

/-- The ideal `Ann_B(M / Bτ)`: the annihilator of the cokernel of `B → M`, `b ↦ b τ`. -/
def cokerSpanIdeal (B : Type*) [CommRing B] [AddCommGroup M] [Module B M] (τ : M) : Ideal B :=
  Module.annihilator B (M ⧸ Submodule.span B {τ})

section Congr

variable {B : Type*} [CommRing B] [AddCommGroup M] [Module B M]

/-- `cokerSpanIdeal B τ` is the annihilator of the `B`-module `M ⧸ Submodule.span B {τ}`. -/
theorem cokerSpanIdeal_def (τ : M) :
    cokerSpanIdeal B τ = Module.annihilator B (M ⧸ Submodule.span B {τ}) := rfl

/-- The ideal is transported by any linear equivalence carrying one section to the other. -/
theorem cokerSpanIdeal_congr {N : Type*} [AddCommGroup N] [Module B N] (e : M ≃ₗ[B] N) {τ : M}
    {σ : N} (h : e τ = σ) : cokerSpanIdeal B τ = cokerSpanIdeal B σ := by
  have hmap : Submodule.map (e : M →ₗ[B] N) (Submodule.span B {τ}) = Submodule.span B {σ} := by
    rw [Submodule.map_span, Set.image_singleton]
    exact congrArg (fun x : N ↦ Submodule.span B {x}) h
  exact LinearEquiv.annihilator_eq
    (Submodule.Quotient.equiv (Submodule.span B {τ}) (Submodule.span B {σ}) e hmap)

end Congr

section BaseChange

variable {B : Type*} [CommRing B] [AddCommGroup M] [Module B M]
variable (B₁ : Type*) [CommRing B₁] [Algebra B B₁]

/-- Base change is right exact on the cokernel of a section: `(B₁ ⊗_B M) / B₁(1 ⊗ τ)` is
`B₁ ⊗_B (M / Bτ)`, `B₁`-linearly. -/
def baseChangeQuotEquiv (τ : M) :
    ((B₁ ⊗[B] M) ⧸ Submodule.span B₁ {(1 : B₁) ⊗ₜ[B] τ}) ≃ₗ[B₁]
      B₁ ⊗[B] (M ⧸ Submodule.span B {τ}) := by
  classical
  set S : Submodule B M := Submodule.span B {τ} with hS
  set W : Submodule B₁ (B₁ ⊗[B] M) := Submodule.span B₁ {(1 : B₁) ⊗ₜ[B] τ} with hW
  have hWker : W ≤ LinearMap.ker (LinearMap.baseChange B₁ S.mkQ) := by
    rw [hW, Submodule.span_le, Set.singleton_subset_iff]
    change (LinearMap.baseChange B₁ S.mkQ) ((1 : B₁) ⊗ₜ[B] τ) = 0
    rw [LinearMap.baseChange_tmul]
    rw [show S.mkQ τ = 0 from
      (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.mem_span_singleton_self τ)]
    exact TensorProduct.tmul_zero _ _
  set ψ₀ : M →ₗ[B] ((B₁ ⊗[B] M) ⧸ W) :=
    (W.mkQ.restrictScalars B).comp (TensorProduct.mk B B₁ M 1) with hψ₀
  have hψ₀ker : S ≤ LinearMap.ker ψ₀ := by
    rw [hS, Submodule.span_le, Set.singleton_subset_iff]
    change ψ₀ τ = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_span_singleton_self _)
  set Φ : ((B₁ ⊗[B] M) ⧸ W) →ₗ[B₁] B₁ ⊗[B] (M ⧸ S) :=
    W.liftQ (LinearMap.baseChange B₁ S.mkQ) hWker with hΦ
  set Ψ : B₁ ⊗[B] (M ⧸ S) →ₗ[B₁] ((B₁ ⊗[B] M) ⧸ W) :=
    LinearMap.liftBaseChange B₁ (S.liftQ ψ₀ hψ₀ker) with hΨ
  have hΨmk : ∀ (b₁ : B₁) (m : M), Ψ (b₁ ⊗ₜ[B] S.mkQ m) = W.mkQ (b₁ ⊗ₜ[B] m) := by
    intro b₁ m
    rw [hΨ, LinearMap.liftBaseChange_tmul]
    change b₁ • W.mkQ ((1 : B₁) ⊗ₜ[B] m) = W.mkQ (b₁ ⊗ₜ[B] m)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hΦmk : ∀ (b₁ : B₁) (m : M), Φ (W.mkQ (b₁ ⊗ₜ[B] m)) = b₁ ⊗ₜ[B] S.mkQ m := by
    intro b₁ m
    rw [hΦ]
    change (LinearMap.baseChange B₁ S.mkQ) (b₁ ⊗ₜ[B] m) = _
    rw [LinearMap.baseChange_tmul]
  refine LinearEquiv.ofLinearMap Φ Ψ (LinearMap.ext fun x ↦ ?_) (LinearMap.ext fun y ↦ ?_)
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b₁ q =>
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective S q
      change Φ (Ψ (b₁ ⊗ₜ[B] S.mkQ m)) = b₁ ⊗ₜ[B] S.mkQ m
      rw [hΨmk, hΦmk]
    | add x y hx hy =>
      change Φ (Ψ (x + y)) = x + y
      rw [map_add, map_add, show Φ (Ψ x) = x from hx, show Φ (Ψ y) = y from hy]
  · obtain ⟨x, rfl⟩ := W.mkQ_surjective y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b₁ m =>
      change Ψ (Φ (W.mkQ (b₁ ⊗ₜ[B] m))) = W.mkQ (b₁ ⊗ₜ[B] m)
      rw [hΦmk, hΨmk]
    | add x y hx hy =>
      change Ψ (Φ (W.mkQ (x + y))) = W.mkQ (x + y)
      rw [map_add, map_add, map_add,
        show Ψ (Φ (W.mkQ x)) = W.mkQ x from hx, show Ψ (Φ (W.mkQ y)) = W.mkQ y from hy]

/-- The ideal of the base-changed section is the annihilator of the base change of the
cokernel. -/
theorem cokerSpanIdeal_tmul_eq (τ : M) :
    cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) =
      Module.annihilator B₁ (B₁ ⊗[B] (M ⧸ Submodule.span B {τ})) :=
  (baseChangeQuotEquiv B₁ τ).annihilator_eq

/-- The extension of `Ann_B(M / Bτ)` to `B₁` is contained in
`Ann_{B₁}((B₁ ⊗_B M) / B₁(1 ⊗ τ))`. -/
theorem map_cokerSpanIdeal_le (τ : M) :
    Ideal.map (algebraMap B B₁) (cokerSpanIdeal B τ) ≤
      cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) := by
  rw [cokerSpanIdeal_tmul_eq, cokerSpanIdeal_def, Ideal.map_le_iff_le_comap]
  exact IsBaseChange.annihilator_le_comap_annihilator
    (TensorProduct.isBaseChange B (M ⧸ Submodule.span B {τ}) B₁)

/-- **Flat base change.** For a flat `B → B₁` and a finite module `M` the extension of
`Ann_B(M / Bτ)` is exactly `Ann_{B₁}((B₁ ⊗_B M) / B₁(1 ⊗ τ))`. This is [Stacks, Tag 07T8]
applied to the cokernel of `τ`. -/
theorem map_cokerSpanIdeal_eq_of_flat [Module.Flat B B₁] [Module.Finite B M] (τ : M) :
    Ideal.map (algebraMap B B₁) (cokerSpanIdeal B τ) =
      cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) := by
  rw [cokerSpanIdeal_tmul_eq, cokerSpanIdeal_def]
  exact ann_extension_eq_ann_baseChange_module

/-- **The closed subsets agree.** For a finite module `M` the closed subset of `Spec B₁` cut
out by `Ann_{B₁}((B₁ ⊗_B M) / B₁(1 ⊗ τ))` is the inverse image of the one cut out by
`Ann_B(M / Bτ)`. This is [Stacks, Tag 00L2] on both sides and [Stacks, Tag 0BUR] in between. -/
theorem zeroLocus_cokerSpanIdeal_tmul [Module.Finite B M] (τ : M) :
    PrimeSpectrum.zeroLocus (cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) : Set B₁) =
      PrimeSpectrum.comap (algebraMap B B₁) ⁻¹'
        PrimeSpectrum.zeroLocus (cokerSpanIdeal B τ : Set B) := by
  rw [cokerSpanIdeal_tmul_eq, cokerSpanIdeal_def, ← Module.support_eq_zeroLocus,
    ← Module.support_eq_zeroLocus]
  exact IsBaseChange.support_eq_preimage_comap
    (TensorProduct.isBaseChange B (M ⧸ Submodule.span B {τ}) B₁)

end BaseChange

section Invertible

variable {B : Type*} [CommRing B] [AddCommGroup M] [Module B M]
variable (B₁ : Type*) [CommRing B₁] [Algebra B B₁]

/-- **Invertible case, the hard inclusion.** If `M` is an invertible `B`-module then
`Ann_{B₁}((B₁ ⊗_B M) / B₁(1 ⊗ τ))` is contained in the extension to `B₁` of the image of
evaluation at `τ` on the dual of `M`. -/
theorem cokerSpanIdeal_tmul_le_map_range_eval [Module.Invertible B M] (τ : M) :
    cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) ≤
      Ideal.map (algebraMap B B₁)
        (LinearMap.range (LinearMap.applyₗ (R := B) (M₂ := B) τ)) := by
  intro a ha
  set I : Ideal B₁ :=
    Ideal.map (algebraMap B B₁) (LinearMap.range (LinearMap.applyₗ (R := B) (M₂ := B) τ)) with hI
  set W : Submodule B₁ (B₁ ⊗[B] M) := Submodule.span B₁ {(1 : B₁) ⊗ₜ[B] τ} with hW
  have hmem : ∀ m : M, a • ((1 : B₁) ⊗ₜ[B] m) ∈ W := by
    intro m
    have h := (Module.mem_annihilator.mp ha) (W.mkQ ((1 : B₁) ⊗ₜ[B] m))
    rw [← map_smul] at h
    exact (Submodule.Quotient.mk_eq_zero W).mp h
  have hτI : ∀ φ : Module.Dual B M, algebraMap B B₁ (φ τ) ∈ I :=
    fun φ ↦ Ideal.mem_map_of_mem _ (LinearMap.mem_range.mpr ⟨φ, rfl⟩)
  have hφ : ∀ (φ : Module.Dual B M) (m : M), a * algebraMap B B₁ (φ m) ∈ I := by
    intro φ m
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmem m)
    have h := congrArg (Module.Dual.baseChange B₁ φ) hc
    simp only [map_smul, Module.Dual.baseChange_apply_tmul, ← Algebra.algebraMap_eq_smul_one,
      smul_eq_mul] at h
    rw [← h]
    exact I.mul_mem_left c (hτI φ)
  have hz : ∀ z : Module.Dual B M ⊗[B] M,
      a * algebraMap B B₁ (contractLeft B M z) ∈ I := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul φ m => simpa only [contractLeft_apply] using hφ φ m
    | add z w hz hw => simpa only [map_add, mul_add] using I.add_mem hz hw
  have hone := hz ((Module.Invertible.linearEquiv B M).symm 1)
  rw [show contractLeft B M ((Module.Invertible.linearEquiv B M).symm 1) = 1 from
    (Module.Invertible.linearEquiv B M).apply_symm_apply 1, map_one, mul_one] at hone
  exact hone

end Invertible

end Stacks.Annihilator

end
