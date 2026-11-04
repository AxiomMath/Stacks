module

public import StacksFrontier.Deformation.SquareZero.Obstruction.RelationDifference
public import StacksFrontier.Deformation.SquareZero.Obstruction.ConormalFunctional
public import StacksFrontier.Deformation.SquareZero.Obstruction.FittingMapOfRelationAgreement
public import StacksFrontier.Deformation.SquareZero.Obstruction.ObstructionClass

/-!
# The obstruction to a map of square-zero deformations

A compatible diagram of square-zero deformation problems has a canonical class in the first
Ext group from the naive cotangent complex.  This class vanishes exactly when the missing map
between the two deformation rings exists.

## Main definitions

* `Stacks.Deformation.obstructionClass` is the canonical obstruction class, bundled with
  its vanishing criterion.

## Main results

The specification of `obstructionClass` says that it vanishes if and only if the deformation
diagram admits a fitting map.

## Implementation notes

The homologically indexed naive cotangent complex is regarded as a cochain complex by putting
its terms in degrees `-1` and `0`.  Universe lifts place that complex and the coefficient module
in a common module category.  The class and its vanishing criterion are bundled in a subtype.

## References

* [Stacks Project, Tag 08S5](https://stacks.math.columbia.edu/tag/08S5)
-/
