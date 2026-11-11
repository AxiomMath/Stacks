module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib states the four parts of Stacks tag 05G5 (base change of finiteness), with clauses
(1) and (2) in the form `S' ⊗[S] M` (resp. an `IsBaseChange` map) rather than the tag's literal
`M ⊗[R] R'`; the literal form is `Module.Finite.tensorBaseChange` and
`Module.FinitePresentation.tensorBaseChange` in `StacksCore.RingTheory.FiniteStability`. -/

@[expose] public section

add_to_stacks 05G5 "part 1, base-change form: applied with base ring `S` and `A = S' = S ⊗[R] R'`,
  a finite `S`-module `M` gives a finite `S'`-module `S' ⊗[S] M`, which is `S'`-isomorphic to
  `M ⊗[R] R'`" Module.Finite.base_change
add_to_stacks 05G5 "part 2, `IsBaseChange` form: applied with base ring `S` and `A = S'`"
  FinitePresentation.of_isBaseChange
add_to_stacks 05G5 "part 3" Algebra.FiniteType.baseChange
add_to_stacks 05G5 "part 4" Algebra.FinitePresentation.baseChange
