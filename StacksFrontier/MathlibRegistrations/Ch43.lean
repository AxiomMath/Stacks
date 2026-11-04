module

public import Mathlib.Algebra.Group.ForwardDiff
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations for Stacks Chapter 43 (Intersection Theory)

Tags of this chapter whose statements are already in Mathlib, registered on the Mathlib
declarations that state them. Where a tag is covered by several declarations, each registration
names the part it gives.
-/

@[expose] public section

add_to_stacks 0AZY "the `r`-th forward difference of `P` is `r! a`"
  Polynomial.fwdDiff_iter_degree_eq_factorial
add_to_stacks 0AZY "the `r`-th forward difference as the alternating sum, at `t - r`"
  fwdDiff_iter_eq_sum_shift
