module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeInitial
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial
import StacksCore.Tactic.StacksAttribute

/-!
# The seminormalization and the weak normalization of a target in a source

For a quasi-compact, quasi-separated, dominant morphism of schemes `f : Y ⟶ X`, the
seminormalization of `X` in `Y` is the initial factorization of `f` through a universal
homeomorphism inducing isomorphisms on all residue fields, and the weak normalization of `X` in
`Y` is the initial factorization of `f` through a universal homeomorphism.

## Implementation notes

Both factorizations have already been constructed, together with their intermediate scheme and
both structural morphisms: `AlgebraicGeometry.seminormalizationFactorization` and
`AlgebraicGeometry.weakNormalizationFactorization`. They are registered here rather than given
new names, since a new name would be a second spelling of the same object. Their initiality and
the defining properties of their maps are supplied where they are constructed.

## References

* [Stacks Project, Tag 0H3P](https://stacks.math.columbia.edu/tag/0H3P)
-/

add_to_stacks 0H3P "part (1)" AlgebraicGeometry.seminormalizationFactorization

add_to_stacks 0H3P "part (2)" AlgebraicGeometry.weakNormalizationFactorization
