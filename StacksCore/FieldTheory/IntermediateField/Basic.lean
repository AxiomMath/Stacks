module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-! # Intermediate fields -/

@[expose] public section

/-- The range of the algebra map from an intermediate field `L` of `E/F` into `E`,
viewed as a subring of `E`, is `L.toSubring`. -/
@[simp]
theorem IntermediateField.range_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E) :
    (algebraMap L E).range = L.toSubring := by ext; simp

@[simp] theorem IntermediateField.map_inj
    {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    (f : E →ₐ[F] K) (E₁ E₂ : IntermediateField F E) :
    E₁.map f = E₂.map f ↔ E₁ = E₂ := (map_injective f).eq_iff
