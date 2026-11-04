module

public import Mathlib.FieldTheory.Normal.Basic
import StacksCore.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Normal field extensions -/

@[expose] public section

open IntermediateField

@[stacks 0BR3]
theorem normal_iff_splits_minpoly_of_adjoin_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {s : Set E} (hs : adjoin F s = ⊤) :
    Normal F E ↔ ∀ x ∈ s, IsAlgebraic F x ∧ ((minpoly F x).map (algebraMap F E)).Splits := by
  refine ⟨fun _ x _ ↦ ⟨Algebra.IsAlgebraic.isAlgebraic _, Normal.splits' _⟩, fun h ↦ ?_⟩
  simp_rw [isAlgebraic_iff_isIntegral] at h
  have : Algebra.IsAlgebraic F E :=
    topEquiv.isAlgebraic_iff.mp <| hs ▸ isAlgebraic_adjoin <| by grind
  exact ⟨fun x ↦ splits_of_mem_adjoin _ _ h <| by simp [hs]⟩

section fieldRange_of_normal
variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

theorem AlgHom.fieldRange_eq_of_normal'
    [Normal F K] (f₁ f₂ : K →ₐ[F] L) : f₁.fieldRange = f₂.fieldRange := by
  algebraize [f₂.toRingHom]
  let K' := f₂.fieldRange
  let e : K ≃ₐ[F] K' := AlgEquiv.ofInjectiveField f₂
  have : Normal F K' := e.transfer_normal.mp ‹_›
  let f' := f₁.comp e.symm.toAlgHom
  simpa [f', fieldRange_comp, e.symm.fieldRange_eq_top, K', ← AlgHom.fieldRange_eq_map]
    using f'.fieldRange_of_normal

variable [Algebra K L] [IsScalarTower F K L]

theorem AlgHom.fieldRange_of_normal'
    [Normal F K] (f : K →ₐ[F] L) : f.fieldRange = (Algebra.algHom F K L).fieldRange :=
  f.fieldRange_eq_of_normal' _

theorem AlgHom.mem_range_of_normal
    [Normal F K] (f : K →ₐ[F] L) (x : K) : f x ∈ Set.range (algebraMap K L) := by
  change f x ∈ (Algebra.algHom F K L).fieldRange
  rw [← f.fieldRange_of_normal']
  simp

theorem AlgHom.exists_algebraMap_of_normal
    [Normal F K] (f : K →ₐ[F] L) (x : K) : ∃ y, f x = algebraMap K L y := by
  simpa [eq_comm] using f.mem_range_of_normal x
