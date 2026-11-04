module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits

/-!
# The standing situation for descending properties along a limit of algebraic spaces

Descending a property from the limit of a directed inverse system of algebraic spaces to a
finite stage of the system starts from one and the same standing situation: a directed inverse
system of quasi-compact and quasi-separated algebraic spaces over a scheme `S` with affine
transition morphisms, a chosen limit of the system, and a chosen index.

## Main results

The situation is `AlgebraicGeometry.Space.DescentSituation`; nothing new is introduced here.

## Implementation notes

Stacks Tags 084R, 09RH and 0CPY fix the same data, so the three tags describe one structure
and no second copy of it is introduced. Tag 0CPY states the situation over the terminal base
scheme only; the structure takes an arbitrary base `S`, so it is the more general form and is
recorded under that tag as well.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 0CPY](https://stacks.math.columbia.edu/tag/0CPY)
-/

add_to_stacks 084R AlgebraicGeometry.Space.DescentSituation
add_to_stacks 0CPY AlgebraicGeometry.Space.DescentSituation
