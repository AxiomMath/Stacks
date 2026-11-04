module

public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # Intermediate fields -/

@[expose] public section

/-- Restricting scalars on an intermediate field along a tower `F₀ → F → E` does not change
the `E`-side rank: `Module.finrank (L.restrictScalars F₀) E = Module.finrank L E`. -/
@[simp]
theorem IntermediateField.finrank_restrictScalars
    {F E : Type*} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    {F₀ : Type*} [Field F₀] [Algebra F₀ F] [Algebra F₀ E] [IsScalarTower F₀ F E] :
    Module.finrank (L.restrictScalars F₀) E = Module.finrank L E := rfl
