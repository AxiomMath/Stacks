module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Base change of the preimage of a submodule along a flat ring map

Let `A → A'` be flat.  For a linear map `ψ : M → Q` whose base change is computed, after
composition with an injective comparison `A' ⊗_A Q → Q'`, by an `A'`-linear `ψ' : M' → Q'`, the
kernel of `ψ'` is spanned by the image of the kernel of `ψ`: base change along a flat map is
exact.

The comparison is injective in the situation that arises for a quasi-coherent module along a
fibre product of affine schemes: `Q = P ⧸ N`, `Q' = P' ⧸ N'`, the base change `A' ⊗_A P → P'` is
bijective, and `N'` is spanned by the image of `N`
(`LinearMap.injective_liftBaseChange_of_quotient`).  Bijectivity of `A' ⊗_A P → P'` follows from
bijectivity of `C' ⊗_C P → P'` when `C' = A' ⊗_A C`
(`LinearMap.bijective_liftBaseChange_restrictScalars_of_isPushout`, in
`StacksFrontier.RingTheory.Flat.EqualizerBaseChange`), and so does the spanning condition
(`Submodule.mem_span_image_of_isPushout`).

## Main results

* `LinearMap.ker_le_span_image_ker_of_flat`
* `LinearMap.injective_liftBaseChange_of_quotient`
* `Submodule.mem_span_image_of_isPushout`
-/

@[expose] public section

open TensorProduct

/-- A commuting square of `A`-linear maps stays commuting after base change to `A'`. -/
private theorem liftBaseChange_baseChange_apply_of_comm {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] {M Q M' Q' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q]
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] [AddCommGroup Q']
    [Module A' Q'] [Module A Q'] [IsScalarTower A A' Q'] (rM : M →ₗ[A] M') (ψ : M →ₗ[A] Q)
    (τ : Q →ₗ[A] Q') (ψ' : M' →ₗ[A'] Q') (hcomm : ∀ m, ψ' (rM m) = τ (ψ m))
    (t : A' ⊗[A] M) :
    τ.liftBaseChange A' (ψ.baseChange A' t) = ψ' (rM.liftBaseChange A' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [hcomm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The kernel of a flat base change is spanned by the base change of the kernel.**  Let
`A → A'` be flat, `rM : M → M'` with surjective base change, `ψ : M → Q`, `τ : Q → Q'` with
injective base change and `ψ' : M' → Q'` with `ψ' ∘ rM = τ ∘ ψ`.  Then the kernel of `ψ'` lies in
the `A'`-span of the image of the kernel of `ψ`. -/
theorem LinearMap.ker_le_span_image_ker_of_flat {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] {M Q M' Q' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup Q] [Module A Q] [AddCommGroup M'] [Module A' M'] [Module A M']
    [IsScalarTower A A' M'] [AddCommGroup Q'] [Module A' Q'] [Module A Q'] [IsScalarTower A A' Q']
    (rM : M →ₗ[A] M') (hrM : Function.Surjective (rM.liftBaseChange A')) (ψ : M →ₗ[A] Q)
    (τ : Q →ₗ[A] Q') (hτ : Function.Injective (τ.liftBaseChange A')) (ψ' : M' →ₗ[A'] Q')
    (hcomm : ∀ m, ψ' (rM m) = τ (ψ m)) :
    LinearMap.ker ψ' ≤ Submodule.span A' (rM '' LinearMap.ker ψ) := by
  intro g' hg'
  obtain ⟨t, rfl⟩ := hrM g'
  have h0 : ψ.baseChange A' t = 0 := hτ (by
    rw [liftBaseChange_baseChange_apply_of_comm rM ψ τ ψ' hcomm, map_zero]; exact hg')
  have hker : t ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor A' A' ψ) := h0
  rw [Module.Flat.ker_lTensor_eq] at hker
  obtain ⟨s, rfl⟩ := hker
  clear hg' h0
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
    simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply,
      LinearMap.liftBaseChange_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, k.2, rfl⟩)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- **Base change of a quotient comparison is injective.**  If `rP : P → P'` has bijective base
change `A' ⊗_A P → P'` and `N' ⊆ P'` lies in the `A'`-span of `rP(N)`, then the map
`τ : P ⧸ N → P' ⧸ N'` induced by `rP` has injective base change. -/
theorem LinearMap.injective_liftBaseChange_of_quotient {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] {P P' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A' P']
    [Module A P'] [IsScalarTower A A' P'] (rP : P →ₗ[A] P')
    (hβ : Function.Bijective (rP.liftBaseChange A')) (N : Submodule A P)
    (N' : Submodule A' P') (hN : N' ≤ Submodule.span A' (rP '' N))
    (τ : (P ⧸ N) →ₗ[A] (P' ⧸ N')) (hτ : ∀ x, τ (N.mkQ x) = N'.mkQ (rP x)) :
    Function.Injective (τ.liftBaseChange A') := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective A' (Submodule.mkQ_surjective N) x
  have hs : rP.liftBaseChange A' s ∈ N' := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
      ← liftBaseChange_baseChange_apply_of_comm rP N.mkQ τ N'.mkQ fun x => (hτ x).symm]
    exact hx
  have hspan : Submodule.span A' (rP '' N) ≤
      (LinearMap.range ((N.subtype).baseChange A')).map (rP.liftBaseChange A') := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨(N.subtype).baseChange A' (1 ⊗ₜ (⟨n, hn⟩ : N)), ⟨_, rfl⟩, by simp⟩
  obtain ⟨s₀, ⟨s₁, rfl⟩, he⟩ := hspan (hN hs)
  rw [← hβ.1 he]
  clear he hs hx
  induction s₁ using TensorProduct.induction_on with
  | zero => simp
  | tmul a k => simp [(Submodule.Quotient.mk_eq_zero N).2 k.2]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **Spans along a pushout.**  If `C' = A' ⊗_A C`, `rP : P → P'` is `C`-linear and `N ⊆ P` is a
`C`-submodule, then the `C'`-span of `rP(N)` lies in its `A'`-span. -/
theorem Submodule.mem_span_image_of_isPushout (A A' C C' : Type*)
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C'] [Algebra A A'] [Algebra A C]
    [Algebra A' C'] [Algebra C C'] [Algebra A C'] [IsScalarTower A A' C'] [IsScalarTower A C C']
    [Algebra.IsPushout A A' C C'] {P P' : Type*} [AddCommGroup P] [Module C P]
    [AddCommGroup P'] [Module A' P'] [Module C P'] [Module C' P'] [IsScalarTower C C' P']
    [IsScalarTower A' C' P'] (rP : P →ₗ[C] P') (N : Submodule C P) {x : P'}
    (hx : x ∈ Submodule.span C' (rP '' N)) : x ∈ Submodule.span A' (rP '' N) := by
  have hC : ∀ (c : C) {y : P'}, y ∈ Submodule.span A' (rP '' N) →
      c • y ∈ Submodule.span A' (rP '' N) := by
    intro c y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨n, hn, rfl⟩
      rw [← map_smul]
      exact Submodule.subset_span ⟨c • n, N.smul_mem c hn, rfl⟩
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro a z _ hz
      have : c • (a • z) = a • (c • z) := by
        rw [← algebraMap_smul C' c, ← algebraMap_smul C' a, ← algebraMap_smul C' c,
          ← algebraMap_smul C' a, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ _ hz
  have hC' : ∀ (c' : C') {y : P'}, y ∈ Submodule.span A' (rP '' N) →
      c' • y ∈ Submodule.span A' (rP '' N) := by
    intro c' y hy
    obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv A A' C C').surjective c'
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, zero_smul]; exact zero_mem _
    | tmul a c =>
      rw [Algebra.IsPushout.equiv_tmul, mul_smul, algebraMap_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ (hC c hy)
    | add t t' ht ht' => rw [map_add, add_smul]; exact add_mem ht ht'
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy; exact Submodule.subset_span hy
  · exact zero_mem _
  · intro a b _ _ ha hb; exact add_mem ha hb
  · intro c' z _ hz; exact hC' c' hz

end
