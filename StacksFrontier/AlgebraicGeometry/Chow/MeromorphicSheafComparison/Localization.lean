module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Regular.SMul

/-!
# Localizing a localization, and localizing at units

Two elementary facts about `IsLocalizedModule`. The first is transitivity: if `f : M → M₁` is a
localization at `S` and `g : M → M₂` is a localization at a larger submonoid `T`, then any map
`M₁ → M₂` through which `g` factors realizes `M₂` as the localization of `M₁` at `T`. The second
is degeneracy: a localization at a submonoid consisting of units is an isomorphism.

## Main results

* `Stacks.Localization.isLocalizedModule_of_comp` — transitivity of localization.
* `Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit` — localizing at units changes
  nothing.
-/

@[expose] public section

namespace Stacks.Localization

variable {R M M₁ M₂ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M] [Module R M₁] [Module R M₂]

/-- Let `f : M → M₁` be a localization at `S` and let `g : M → M₂` be a localization at a
submonoid `T` containing `S`. If `h : M₁ → M₂` satisfies `h ∘ f = g`, then `h` exhibits `M₂` as
the localization of `M₁` at `T`. -/
theorem isLocalizedModule_of_comp {S T : Submonoid R} (hST : S ≤ T)
    (f : M →ₗ[R] M₁) (g : M →ₗ[R] M₂) (h : M₁ →ₗ[R] M₂)
    (hcomp : ∀ m, h (f m) = g m)
    [IsLocalizedModule S f] [IsLocalizedModule T g] :
    IsLocalizedModule T h where
  map_units t := IsLocalizedModule.map_units g t
  surj z := by
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj T g z
    exact ⟨⟨f m, t⟩, by rw [ht, hcomp]⟩
  exists_of_eq {a b} hab := by
    obtain ⟨⟨m₁, s₁⟩, hs₁⟩ := IsLocalizedModule.surj S f a
    obtain ⟨⟨m₂, s₂⟩, hs₂⟩ := IsLocalizedModule.surj S f b
    simp only [Submonoid.smul_def] at hs₁ hs₂
    have key : g ((s₂ : R) • m₁) = g ((s₁ : R) • m₂) := by
      rw [map_smul, map_smul, ← hcomp m₁, ← hcomp m₂, ← hs₁, ← hs₂, map_smul, map_smul, hab,
        smul_comm]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) key
    simp only [Submonoid.smul_def] at ht
    refine ⟨t * ⟨s₁, hST s₁.2⟩ * ⟨s₂, hST s₂.2⟩, ?_⟩
    have h2 := congrArg f ht
    simp only [map_smul, ← hs₁, ← hs₂] at h2
    simp only [Submonoid.smul_def, mul_smul]
    rwa [smul_comm (s₁ : R) (s₂ : R) a]

/-- A localization at a submonoid consisting of units is bijective. -/
theorem bijective_of_isLocalizedModule_of_isUnit {S : Submonoid R} (f : M →ₗ[R] M₁)
    [IsLocalizedModule S f] (hS : ∀ s ∈ S, IsUnit s) : Function.Bijective f := by
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) hab
    simp only [Submonoid.smul_def] at hs
    exact (hS s s.2).isSMulRegular M hs
  · obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S f z
    simp only [Submonoid.smul_def] at hs
    obtain ⟨u, hu⟩ := hS s s.2
    refine ⟨(↑u⁻¹ : R) • m, ?_⟩
    rw [map_smul, ← hs, smul_smul, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end Stacks.Localization
