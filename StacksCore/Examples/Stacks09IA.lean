module

import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.NumberTheory.FunctionField
public import StacksCore.FieldTheory.PurelyTranscendental
import StacksCore.FieldTheory.RatFunc.AsPolynomial

/-! # Non-unique decomposition into purely transcendental and algebraic extensions -/

@[expose] public section

universe u

open IntermediateField RatFunc

/-- **Stacks 09IA**.
The decomposition of an extension `E/F` as a purely transcendental extension followed by an
algebraic one is not unique. Concretely, taking `E = F(t)`, both `F(t)` and `F(t^2)` are
intermediate fields that are purely transcendental over `F` and over which `E` is algebraic, yet
they are distinct. -/
@[stacks 09IA]
theorem exists_intermediateField_purelyTranscendental_and_algebraic_ne
    (F : Type u) [Field F] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (K L : IntermediateField F E),
    PurelyTranscendental F K ∧ Algebra.IsAlgebraic K E ∧
    PurelyTranscendental F L ∧ Algebra.IsAlgebraic L E ∧
    K ≠ L :=
  have := FunctionField.finiteDimensional_of_adjoin_transcendental (transcendental_X (K := F))
  have := FunctionField.finiteDimensional_of_adjoin_transcendental
    ((transcendental_X (K := F)).pow (by grind : 0 < 2))
  ⟨RatFunc F, inferInstance, inferInstance, F⟮ X⟯, F⟮X ^ 2⟯,
    transcendental_X.purelyTranscendental_adjoin, .of_finite _ _,
    (transcendental_X.pow (by grind)).purelyTranscendental_adjoin, .of_finite _ _,
    fun h ↦ by simpa [finrank_eq_max_natDegree] using congr(Module.finrank $h F⟮X⟯)⟩
