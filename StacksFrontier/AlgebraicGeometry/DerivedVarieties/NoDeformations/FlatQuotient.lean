module

public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of the quotient by a fibrewise regular sequence

For a flat local homomorphism of local rings which is essentially of finite presentation, a
sequence of elements of the target that is regular on the closed fibre cuts out a quotient that is
flat over the base. This is the ring case of the module statement
`Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`, which the
repository already proves; this file only records the Stacks tag on it.

## Main results

* `Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal` gives flatness
  of every partial quotient, including the full quotient.

## Implementation notes

Taking the module to be the target ring and the sequence to be the lifted elements gives the
flatness asserted here. The Koszul complex and its deformation do not enter the flatness argument.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0470](https://stacks.math.columbia.edu/tag/0470)
-/

add_to_stacks 0G0N "flat_quotient"
  Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
