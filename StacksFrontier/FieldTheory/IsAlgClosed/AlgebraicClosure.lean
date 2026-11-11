module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of an algebraic closure

This file states Stacks Theorem 09GT: every field has an algebraic closure, that is
(Stacks Definition 09GS) an extension field which is algebraic over it and algebraically
closed. Mathlib's `AlgebraicClosure k` is such an extension, so the theorem follows from
the instance `AlgebraicClosure.isAlgClosure`.
-/

@[expose] public section

universe u

/-- **Stacks 09GT**.
Every field `k` has an algebraic closure: there is a field `K` with a `k`-algebra structure
(an extension of `k`) such that `K` is algebraic over `k` and algebraically closed. -/
@[stacks 09GT]
theorem exists_isAlgClosure (k : Type u) [Field k] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsAlgClosure k K :=
  ⟨AlgebraicClosure k, inferInstance, inferInstance, inferInstance⟩
