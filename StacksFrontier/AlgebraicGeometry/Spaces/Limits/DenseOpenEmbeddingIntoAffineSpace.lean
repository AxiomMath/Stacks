module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace.ComponentImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace.ComponentGlueing

/-!
# A dense open of a finitely presented algebraic space immerses into affine space

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `X` Noetherian and `f` of
finite presentation.  Then `Y` has a dense open subspace `V` admitting an immersion into
relative affine space `𝔸ⁿ_X` over `X`.  Finite presentation makes `Y` Noetherian, so its
space of points has finitely many irreducible components; over the generic point of each
component the morphism factors, after shrinking, through a scheme-theoretic image whose
schematic locus is a scheme, and there Stacks 04II produces an immersion into affine space.
The pieces are disjoint opens, so they glue to a dense open of `Y`, and the resulting
immersion into a coproduct of affine spaces is composed with an immersion of that coproduct
into a single affine space.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpen_isImmersion_affineSpaceOver` is **Stacks 088N**.

## Implementation notes

An open subspace is a subfunctor whose inclusion is an open immersion; density is density of
the range of its map on points for the point topology of Stacks 03BX.  Relative affine space
is the product presheaf `AlgebraicGeometry.Space.affineSpaceOver`, and the equation with its
first projection records that the immersion is a morphism over `X`.

## References

* [Stacks Project, Tag 088N](https://stacks.math.columbia.edu/tag/088N)
-/
