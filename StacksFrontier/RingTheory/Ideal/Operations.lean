module

public import Mathlib.RingTheory.Ideal.Operations

import StacksCore.Tactic.StacksAttribute

/-!
# Prime avoidance, and products of ideals in a prime ideal

Mathlib already states both tags of this file.

Stacks 00DS is prime avoidance: for ideals `I i` indexed by a finset `s`, all but two of them
prime, and an ideal `J` contained in none of them, there is an `x ∈ J` lying in no `I i`. This
is `Ideal.subset_union_prime`, in the equivalent covering form — `J` is contained in the union
of the `I i` exactly when it is contained in one of them — of which the tag's statement is the
contrapositive. That declaration already carries the tag upstream, so nothing is recorded for
it here.

Stacks 07K1 — a prime ideal containing `I * J` contains `I` or `J` — is
`Ideal.IsPrime.mul_le`.
-/

@[expose] public section

add_to_stacks 07K1 Ideal.IsPrime.mul_le
