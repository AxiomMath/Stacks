module

public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Construction
public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Properties
public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.NormalizationAndGenus

/-!
# The pinched projective line over a finite field extension

Let `K/k` be a nontrivial finite extension of fields. Gluing `Spec A`, for `A` the subring of
`K[X]` of polynomials whose constant coefficient lies in `k`, to `Spec K[Y]` along
`Spec K[T, T⁻¹]` by inversion of the coordinate produces a proper curve over `k` which is
singular at exactly one point, has `k` for its ring of global functions, has genus zero, and
whose normalization is the projective line over `K`. This is the standard example of a proper
curve over a field which is not geometrically reduced after the singular point is removed, and
of a genus-zero curve with no rational point.

## Main definitions

None; the curve and its charts are produced by the existence statement below.

## Main results

* `AlgebraicGeometry.exists_pinchedProjectiveLine` produces the curve together with its two
  affine charts, its gluing datum, its singular point, its global functions, its genus and its
  normalization.

## Implementation notes

The curve is built with `CategoryTheory.GlueData'` from the two affine charts and the single
overlap `Spec K[T, T⁻¹]`, so that the gluing datum of the statement is realized on the nose:
the two chart inclusions are the canonical maps out of the glued scheme, and the overlap is
their fibre product. Properness is obtained by descending universal closedness along the
surjection from the projective line over `K`, whose own universal closedness comes from the
valuative criterion applied chart by chart; separatedness and the vanishing of the first
cohomology both come from the fact that a Laurent polynomial is the sum of an element of `A`
and a polynomial in `T⁻¹`. The normalization is identified with the canonical normalization
morphism of Tag 035N, not merely with some finite birational map, by combining Tag 035Q with
triviality of the normalization of a normal scheme.

## References

* [Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC)
-/
