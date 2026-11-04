module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
import StacksCore.Tactic.StacksAttribute

/-! # Operations on quotients by ideals -/

-- 00DT (1) second half: `R/(I₁ ⋯ I_r) ≅ R/I₁ × … × R/I_r`. Mathlib states it for any
-- `Finite` index type and in the `⨅` spelling; `Ideal.prod_eq_iInf_of_pairwise_isCoprime`
-- (attributed in `StacksCore/RingTheory/Ideal/Operations.lean`) converts that to the tag's `∏`.
add_to_stacks 00DT "(1)" Ideal.quotientInfRingEquivPiQuotient

@[expose] public section

/-- The isomorphism `(A ⧸ ker f) ≃ₐ range f` sends the class of `x : A` to `f x`. -/
@[simp] theorem Ideal.quotientKerEquivRange_mk
    {R A B : Type*} [CommSemiring R] [Ring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (x : A) : Ideal.quotientKerEquivRange f x = f x := rfl
