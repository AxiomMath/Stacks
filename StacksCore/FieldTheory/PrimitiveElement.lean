module

public import Mathlib.FieldTheory.PrimitiveElement

/-! # Primitive element theorem -/

@[expose] public section

open IntermediateField

/-- Primitive element theorem for intermediate fields: a finite-dimensional intermediate
field `E` of a separable extension `L/K` is generated over `K` by a single element of `L`. -/
theorem IntermediateField.exists_primitive_element
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : ∃ x ∈ E, K⟮x⟯ = E := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K E
  exact ⟨x, x.2, by simpa using congr(lift $hx)⟩
