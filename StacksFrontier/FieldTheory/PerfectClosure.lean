module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCore.Tactic.StacksAttribute

/-!
# The perfect closure of a field

Stacks 046X names the purely inseparable extension of Stacks 046W the *perfect closure* of `k`,
written `k^perf`. Mathlib has it as `perfectClosure k E`, the largest purely inseparable
subextension of `E/k` — maximal by `le_perfectClosure_iff` — which for `E` an algebraic closure
of `k` is the tag's field, perfect by `perfectClosure.perfectField`.

Note that Mathlib's unrelated `PerfectClosure k p` is the perfection of `k`, a colimit of copies
of `k` along the Frobenius, and not this object.
-/

@[expose] public section

add_to_stacks 046X "the perfect closure of `k`, as the largest purely inseparable subextension
  of a given extension; the tag's `k^perf` is this taken inside an algebraic closure"
  perfectClosure
add_to_stacks 046X "that it is a perfect field" perfectClosure.perfectField
