module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.ElementaryReplacementComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.Coresolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.ReplacementAbove
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.DescentAndFreeze

/-!
# Resolutions by objects of bounded cohomological dimension

Let `A` be an abelian category and `d : A → ℕ∞` a function such that every object embeds into
an object of `d`-value `0`, `d (X ⊞ Y) ≤ max (d X) (d Y)`, and for every short exact sequence
`0 → X₁ → X₂ → X₃ → 0` one has `d X₃ ≤ max (d X₁ - 1) (d X₂)`. If `K` is a cochain complex with
`n + d (K.X n) → -∞` as `n → -∞`, then there is a quasi-isomorphism `K ⟶ L` with
`d (L.X n) = 0` for all `n`.

The development is split into:

* `ElementaryReplacementComplex`: the hypotheses on `d` and the elementary replacement complex.
* `Coresolution`: the elementary replacement theorems and `d`-acyclic coresolutions.
* `ReplacementAbove`: replacement above a degree, reduction to finite `d`-values, and one
  descent step.
* `DescentAndFreeze`: the descent sequence, the frozen limit complex, and the main result
  `exists_dZero_qis`.

## References

* [Stacks: Tag 07K6](https://stacks.math.columbia.edu/tag/07K6)
-/
