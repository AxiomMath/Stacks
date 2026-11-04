module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers

/-! ## Opposite Equalizers -/

@[expose] public section

open CategoryTheory.Limits

/-- Coequalizers in `C` correspond to equalizers of the opposite morphisms in `Cᵒᵖ`. -/
theorem CategoryTheory.hasCoequalizer_iff_hasEqualizer_op {D : Type*} [Category* D] {X Y : D}
    (f g : X ⟶ Y) : HasCoequalizer f g ↔ HasEqualizer f.op g.op := by
  refine ⟨fun _ ↦ hasLimit_of_iso (parallelPairOpIso f g).symm, fun _ ↦ ?_⟩
  have := hasLimit_of_iso (parallelPairOpIso f g)
  have : HasLimit (parallelPair f g).op :=
    hasLimit_of_equivalence_comp walkingParallelPairOpEquiv
  exact hasColimit_of_hasLimit_op (parallelPair f g)
