module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 05G5 via multiple decls. -/

@[expose] public section

add_to_stacks 05G5 "part 1" Module.Finite.tensorProduct
add_to_stacks 05G5 "part 2" FinitePresentation.of_isBaseChange
add_to_stacks 05G5 "part 3" Algebra.FiniteType.baseChange
add_to_stacks 05G5 "part 4" Algebra.FinitePresentation.baseChange
