module

public import Mathlib.Order.Category.PartOrd
import StacksCore.Tactic.StacksAttribute

/-! # Directed limits and colimits
This file adds stacks tags to various mathlib declarations around limits and colimits over
preordered and in particular directed sets.
-/

@[expose] public section

add_to_stacks 00D3 Preorder
add_to_stacks 00D3 PartialOrder
add_to_stacks 00D3 "Directed sets. Note that unlike stacks, mathlib does not require directed sets
  to be nonempty." IsDirectedOrder

add_to_stacks 0030 "The instance giving every preordered set the structure of a category. Inductive
  and inverse systems are just functors out of a poset resp. its opposite with respect to this."
  Preorder.smallCategory

add_to_stacks 0CN1 "The partial order quotient of a preorder." Antisymmetrization
add_to_stacks 0CN1 "The partial order quotient construction as a functor." preordToPartOrd

add_to_stacks 0031 "A directed system is just a functor out of a nonempty directed order;
  this should not be bundled." IsDirectedOrder
