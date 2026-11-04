module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget

/-!
# A degree bound read off from the field-valued base changes

An integer bounds the degrees of the fibres of a morphism of schemes exactly when every base
change of that morphism along a morphism from the spectrum of a field is finite locally free of
some rank at most that integer. This module declares nothing: it imports that equivalence,
`AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`.
-/
