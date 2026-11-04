module

public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeUH.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksCore.Tactic.StacksAttribute

/-!
# Integrality of the normalization base-change comparison

Let `X` be a scheme locally of finite type over a field `k` and let `K/k` be an extension of
fields. The comparison morphism of Tag 0C3N from the normalization of `X_K` to the base change of
the normalization of `X` is an integral morphism.

That statement, `AlgebraicGeometry.isIntegralHom_normalizationBaseChangeComparison`, and the
identification `AlgebraicGeometry.baseChangeNormalization_eq` of the base change of the
normalization morphism with a pullback projection, are proved in
`StacksFrontier/AlgebraicGeometry/NormalizationBaseChangeUH/Basic.lean`, where the integrality
is moreover an `instance` and the reductions of Tag 0C3N that it unlocks are recorded. This file
re-exports them, so that the consumers written against it are unaffected.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/
