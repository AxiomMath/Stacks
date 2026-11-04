module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Localization of modules -/
add_to_stacks 07JZ LocalizedModule
add_to_stacks 07K0 IsLocalizedModule.lift_unique

@[expose] public section

universe u v

lemma LocalizedModule.mk_cancel' {R : Type u} [CommSemiring R] {S : Submonoid R} {M : Type v}
    [AddCommMonoid M] [Module R M] (s : ↥S) (m : M) :
  mk (s.1 • m) s = mk m 1 := mk_cancel ..

/-- Localization preserves invertibility of scalar actions: if `r : R` acts invertibly on
`N`, then it acts invertibly on `LocalizedModule S N`. -/
theorem LocalizedModule.isUnit_algebraMap_end_of_isUnit {R : Type u} [CommSemiring R]
    (S : Submonoid R) {N : Type v} [AddCommMonoid N] [Module R N] {r : R}
    (h : IsUnit (algebraMap R (Module.End R N) r)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S N)) r) := by
  rw [Module.End.isUnit_iff] at h ⊢
  refine ⟨fun z₁ z₂ ↦ ?_, fun z ↦ ?_⟩
  · induction z₁, z₂ using induction_on₂ with | _ n n' s s' =>
    simp only [Module.algebraMap_end_apply, smul'_mk, mk_eq]
    exact fun ⟨u, hu⟩ ↦ ⟨u, h.injective <| by simpa using hu⟩
  · induction z with | h n s =>
    obtain ⟨n', hn'⟩ := h.surjective n
    rw [Module.algebraMap_end_apply] at hn'
    exact ⟨mk n' s, by rw [Module.algebraMap_end_apply, smul'_mk, hn']⟩
