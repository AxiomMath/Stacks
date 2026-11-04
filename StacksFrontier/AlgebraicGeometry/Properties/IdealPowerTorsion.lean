module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Submodules annihilated by powers of an ideal

For an ideal `I` of a commutative ring and a module `M`, the elements annihilated by every
element of `I ^ n` form a submodule of `M`.

## Main definitions

* `Submodule.torsionBySet A M (I ^ n : Ideal A)` is the submodule of elements annihilated by a
  specified power of an ideal.

## Implementation notes

Mathlib's `Submodule.torsionBySet` is the submodule `Mₙ` of the source. Apply it to the set
underlying `I ^ n`; its membership characterization `Submodule.mem_torsionBySet_iff` says that
every element of `I ^ n` annihilates the member.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

add_to_stacks 01PM "i_power_annihilator_submodules" Submodule.torsionBySet

end
