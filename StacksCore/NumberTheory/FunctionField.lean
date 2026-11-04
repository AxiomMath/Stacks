module

public import Mathlib.NumberTheory.FunctionField

/-! # Function fields -/

@[expose] public section

open IntermediateField algebraAdjoinAdjoin

/-- In a function field `K` over `F`, any element `y ∈ K` that is transcendental over `F`
gives a singleton transcendence basis of `K/F`: the constant family `_ ↦ y` indexed by a
unique type is algebraically independent and `K` is algebraic over `F(y)`. -/
theorem Transcendental.isTranscendenceBasis
    {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra (RatFunc F) K] [IsScalarTower F (RatFunc F) K] [FunctionField F K]
    {y : K} (hy : Transcendental F y) [Unique ι] :
    IsTranscendenceBasis F (fun _ : ι ↦ y) := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨?_, ?_⟩
  · exact algebraicIndependent_unique_type_iff.mpr hy
  · have := FunctionField.finiteDimensional_of_adjoin_transcendental hy
    rw [Set.range_const]
    exact .trans _ F⟮y⟯ _
