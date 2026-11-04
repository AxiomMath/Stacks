module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Uniformity of eventual vanishing after flat base change

Let `φₖ : P → Qₖ` (`k ≥ m`) be maps out of a Noetherian module with `φₖ' = tₖₖ' ∘ φₖ` for
`k ≤ k'`. Their kernels increase with `k`, hence stabilize. Whether `φₖ` vanishes after a flat
base change `S ⊗ -`, and the kernel and image of `S ⊗ φₖ`, depend only on `ker φₖ`. So once the
kernels have stabilized, a property of the base changed maps that holds for one large `k` holds
for all `k` beyond the stabilization index, and that index does not depend on `S`.

This is the mechanism that makes the per-prime bounds of Stacks Tag 0EFX uniform: there the maps
are `Extʲ(IᵐM, ω) → Extʲ(IᵏM, ω)` and `S` is the completion of a localization of the base ring.

## Main results

* `LinearMap.lTensor_eq_zero_iff_subsingleton_quotient_ker`,
  `LinearMap.ker_lTensor_eq_of_ker_eq`, `LinearMap.range_lTensor_comp_eq_iff` — for a flat
  module these properties depend only on the kernel.
* `Module.exists_ker_stable` — the stabilization of the kernels.
-/

@[expose] public section

open TensorProduct

universe u v w x

variable {R : Type u} [CommRing R] (S : Type v) [AddCommGroup S] [Module R S] [Module.Flat R S]
variable {P Q Q' P₀ : Type w} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup Q'] [Module R Q'] [AddCommGroup P₀] [Module R P₀]

namespace LinearMap

/-- The factorization `P → P / ker φ ↪ Q` of a linear map. -/
private theorem eq_kerLift_comp (φ : P →ₗ[R] Q) :
    φ = (LinearMap.ker φ).liftQ φ le_rfl ∘ₗ (LinearMap.ker φ).mkQ := by
  ext x; rfl

/-- After a flat base change, `S ⊗ φ` factors as a surjection followed by an injection through
`S ⊗ (P / ker φ)`. -/
private theorem lTensor_factor (φ : P →ₗ[R] Q) :
    Function.Injective (((LinearMap.ker φ).liftQ φ le_rfl).lTensor S) ∧
      Function.Surjective ((LinearMap.ker φ).mkQ.lTensor S) ∧
      φ.lTensor S = ((LinearMap.ker φ).liftQ φ le_rfl).lTensor S ∘ₗ
        (LinearMap.ker φ).mkQ.lTensor S :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap _
      (LinearMap.ker_eq_bot.mp ((LinearMap.ker φ).ker_liftQ_eq_bot' φ rfl)),
    LinearMap.lTensor_surjective S (Submodule.mkQ_surjective _),
    by rw [← LinearMap.lTensor_comp, ← eq_kerLift_comp]⟩

/-- After a flat base change, a map vanishes exactly when `S ⊗ (P / ker φ)` does. -/
theorem lTensor_eq_zero_iff_subsingleton_quotient_ker (φ : P →ₗ[R] Q) :
    φ.lTensor S = 0 ↔ Subsingleton (S ⊗[R] (P ⧸ LinearMap.ker φ)) := by
  obtain ⟨hι, hπ, hφ⟩ := lTensor_factor S φ
  set K := LinearMap.ker φ
  set ι := K.liftQ φ le_rfl
  constructor
  · intro h
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    apply hι
    have ha := LinearMap.congr_fun h a'
    have hb := LinearMap.congr_fun h b'
    rw [hφ] at ha hb
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  · intro h
    refine LinearMap.ext fun x ↦ ?_
    rw [hφ, LinearMap.comp_apply, LinearMap.zero_apply,
      Subsingleton.elim ((K.mkQ).lTensor S x) 0, map_zero]

/-- After a flat base change, the kernel of a map is the base change of its kernel. -/
theorem ker_lTensor_eq_range (φ : P →ₗ[R] Q) :
    LinearMap.ker (φ.lTensor S) = LinearMap.range ((LinearMap.ker φ).subtype.lTensor S) := by
  have h := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map φ)
  exact (LinearMap.exact_iff.mp h)

/-- After a flat base change, the kernel of a map depends only on its kernel. -/
theorem ker_lTensor_eq_of_ker_eq (φ : P →ₗ[R] Q) (φ' : P →ₗ[R] Q')
    (h : LinearMap.ker φ = LinearMap.ker φ') :
    LinearMap.ker (φ.lTensor S) = LinearMap.ker (φ'.lTensor S) := by
  rw [ker_lTensor_eq_range, ker_lTensor_eq_range, h]

/-- After a flat base change, `φ ∘ ψ` and `φ` have the same image exactly when the composite of
`ψ` with `P → P / ker φ` becomes surjective. -/
theorem range_lTensor_comp_eq_iff (φ : P →ₗ[R] Q) (ψ : P₀ →ₗ[R] P) :
    LinearMap.range ((φ ∘ₗ ψ).lTensor S) = LinearMap.range (φ.lTensor S) ↔
      Function.Surjective (((LinearMap.ker φ).mkQ ∘ₗ ψ).lTensor S) := by
  obtain ⟨hι, hπ, h2⟩ := lTensor_factor S φ
  set K := LinearMap.ker φ
  set ι := K.liftQ φ le_rfl
  have h1 : (φ ∘ₗ ψ).lTensor S = ι.lTensor S ∘ₗ ((K.mkQ ∘ₗ ψ).lTensor S) := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [h1, h2, LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hπ]
  constructor
  · intro h
    rw [← LinearMap.range_eq_top]
    exact Submodule.map_injective_of_injective hι h
  · intro h
    rw [LinearMap.range_eq_top.mpr h]

end LinearMap

/-- **Kernels of a compatible family out of a Noetherian module stabilize.** If `φ k : P → Q k`
satisfies `φ k' = t k k' ∘ φ k` for `m ≤ k ≤ k'`, there is `k₁ ≥ m` with
`ker φ k = ker φ k₁` for every `k ≥ k₁`. -/
theorem Module.exists_ker_stable [IsNoetherian R P] {Qf : ℕ → Type w}
    [∀ k, AddCommGroup (Qf k)] [∀ k, Module R (Qf k)] (m : ℕ) (φ : ∀ k, P →ₗ[R] Qf k)
    (t : ∀ k k', k ≤ k' → Qf k →ₗ[R] Qf k')
    (ht : ∀ k k' (h : k ≤ k'), m ≤ k → φ k' = t k k' h ∘ₗ φ k) :
    ∃ k₁, m ≤ k₁ ∧ ∀ k, k₁ ≤ k → LinearMap.ker (φ k) = LinearMap.ker (φ k₁) := by
  let f : ℕ →o Submodule R P := ⟨fun n ↦ LinearMap.ker (φ (m + n)), fun a b hab ↦ by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [ht (m + a) (m + b) (by omega) (by omega), LinearMap.comp_apply, hx, map_zero]⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨m + n, by omega, fun k hk ↦ ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
  exact (hn d (by omega)).symm
