module

public import Mathlib.Algebra.Module.Projective
import StacksCore.Tactic.StacksAttribute

/-! Projective modules -/

@[expose] public section

add_to_stacks 09FP Module.projective_lifting_property

universe u v v'

/-- This is a generalisation of 07JX to an characterization of projective modules, the forward
direction is exactly what 07JX states. -/
@[stacks 07JX]
theorem Module.projective_iff_lift_map_range_le
    {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔ ∀ {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M]
      [Module R N] (α : P →ₗ[R] M) (β : N →ₗ[R] M), LinearMap.range α ≤ LinearMap.range β →
      ∃ γ : P →ₗ[R] N, α = β.comp γ := by
  refine ⟨fun _ _ _ _ _ _ _ α β h ↦ ?_, fun H ↦ .of_lifting_property' fun {M} N _ _ _ _ f g hf ↦ ?_⟩
  · obtain ⟨γ, hγ⟩ := Module.projective_lifting_property β.rangeRestrict
      (LinearMap.codRestrict (LinearMap.range β) α fun x ↦ h (LinearMap.mem_range_self α x))
      (LinearMap.surjective_rangeRestrict β)
    exact ⟨γ, by simpa [LinearMap.ext_iff, Subtype.ext_iff, eq_comm] using hγ⟩
  obtain ⟨γ, hγ⟩ := H g f (by grw [f.range_eq_top_of_surjective hf, ← le_top])
  exact ⟨γ, hγ.symm⟩
