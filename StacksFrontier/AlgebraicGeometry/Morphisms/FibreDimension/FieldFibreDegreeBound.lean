module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange

/-!
# Fibre degree bounds tested on field-valued base changes

An integer bounds the degrees of the fibres of a morphism of schemes `f : X ⟶ Y` exactly when
every base change of `f` to the spectrum of a field is finite locally free of rank at most that
integer.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`: a bound on the degrees of the
  fibres of `f` is the same thing as a bound on the ranks of all base changes of `f` to spectra
  of fields.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/
