module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import StacksCore.Tactic.StacksAttribute

/-! # Connected limits -/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 002T Over.preservesLimitsOfShape_forget_of_isConnected

add_to_stacks 04AR Under.preservesColimitsOfShape_forget_of_isConnected
