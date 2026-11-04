module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf

/-!
# Isomorphisms between objects presented in a quotient stack (Stacks 044V)

Let `G` be a groupoid in algebraic spaces `(U, R, s, t, c)` over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `[U/R]` be its quotient stack (**Stacks 044Q**). Two points
`x, y` of the object space `U` over a test object `T` present two objects of `[U/R]` over `T`.
Stacks 044V says that the sheaf of isomorphisms between those two objects is the fibre product
`R ×_{(t, s), U ×_S U, (y, x)} T`, i.e. the arrow space pulled back along the pair of points.

That statement, together with the arrow fibre `AlgebraicGeometry.Stack.arrowFiber`, the
canonicity property `AlgebraicGeometry.Stack.IsCanonicalArrowFiberIso`, the identification
`AlgebraicGeometry.Stack.isomPresheafPullbackIso` and its two component descriptions, is proved
in `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf` and
re-exported here, so that consumers of this module resolve every one of those names unchanged.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/
