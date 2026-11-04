module

public import Mathlib.Algebra.Central.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 11 (Brauer Groups) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

## Tags

* 0742: a `k`-algebra is central if its center is the image of `k`; Mathlib's
  `Algebra.IsCentral` asks `Subalgebra.center K D ≤ ⊥`, and `⊥` is the image of `algebraMap`.
-/

add_to_stacks 0742 Algebra.IsCentral
