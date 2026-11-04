module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Characterization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.DimensionBound

/-!
# A finite-dimensional Noetherian scheme has an affine stratification of length its dimension

A Noetherian scheme of dimension at most `d` admits an affine stratification indexed by
`0, …, d`.

## Main results

* `AlgebraicGeometry.nonempty_affineStratification_of_topologicalKrullDim_le`: a Noetherian
  scheme with `topologicalKrullDim X ≤ d` has an affine stratification indexed by `Fin (d + 1)`.

## Implementation notes

The affine stratification number of [Stacks, Tag 0F2V] is the least `n` admitting an affine
stratification indexed by `0, …, n`, so the bound `affineStratificationNumber X ≤ d` asserts that
`X` has an affine stratification indexed by `0, …, d`. Here `affineStratificationNumber` is an
infimum in `ℕ`, which is zero for a scheme with no finite affine stratification, so the inequality
`affineStratificationNumber_le_of_topologicalKrullDim` alone does not produce a stratification;
the existence is stated directly.

Finite dimension is expressed as an inequality `topologicalKrullDim X ≤ d` with `d` a natural
number, which excludes infinite dimension; the empty scheme is allowed.

## References

* [Stacks Project, Tag 0F2X](https://stacks.math.columbia.edu/tag/0F2X)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A Noetherian scheme of dimension at most `d` has an affine stratification indexed by
`0, …, d`; that is, its affine stratification number is at most `d` in the sense of
[Stacks, Tag 0F2V]. -/
@[stacks 0F2X "an affine stratification indexed by 0, …, d exists"]
theorem nonempty_affineStratification_of_topologicalKrullDim_le (X : Scheme.{u})
    [IsNoetherian X] (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    Nonempty (AffineStratification X (Fin (d + 1))) :=
  (affineStratificationNumber_le_iff X d).1
    (affineStratificationNumber_le_of_topologicalKrullDim X d hdim)

end AlgebraicGeometry

end
