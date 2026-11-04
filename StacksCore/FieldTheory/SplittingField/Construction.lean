module

public import Mathlib.FieldTheory.SplittingField.Construction
import StacksCore.Tactic.StacksAttribute

/-! # Splitting fields -/

@[expose] public section

add_to_stacks 09HU "smallest" Polynomial.SplittingField.lift
add_to_stacks 09HU "unique up to (not necessarily unique) isomorphism"
  Polynomial.IsSplittingField.algEquiv
