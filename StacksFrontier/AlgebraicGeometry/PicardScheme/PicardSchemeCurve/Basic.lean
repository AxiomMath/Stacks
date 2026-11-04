module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Genus of a smooth projective curve

The genus of a smooth projective geometrically irreducible curve over a field is the
dimension over that field of the first cohomology of its structure sheaf. That invariant is
`AlgebraicGeometry.genus`, which is defined for an arbitrary scheme over a field: it computes
the dimension of first structure-sheaf cohomology through the right-derived functor of global
sections, retaining the module structure over the specified ground field.

## Implementation notes

Smoothness, projectivity, geometric irreducibility and being a curve are conditions on the
intended domain of use, not arguments needed to form the invariant, so no separate definition
is introduced here. Tag 0B9W is therefore recorded as an attribute on `AlgebraicGeometry.genus`
itself, in `StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic`, alongside the more general
Tag 0BY7; this module declares nothing of its own.

## References

* [Stacks Project, Tag 0B9W](https://stacks.math.columbia.edu/tag/0B9W)
-/
