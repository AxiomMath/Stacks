module

public import Mathlib.CategoryTheory.Presentable.Finite
import StacksCore.Tactic.StacksAttribute

/-! # Categorically compact objects
This file adds stacks tags from section 4.26: categorically compact objects to an
existing declaration.
-/

@[expose] public section

open CategoryTheory

add_to_stacks 0FWX IsFinitelyPresentable
