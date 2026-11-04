module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import StacksCore.Tactic.StacksAttribute

/-! `ZMod p` is a field -/

@[expose] public section

add_to_stacks 09FH "first part" ZMod.instField
