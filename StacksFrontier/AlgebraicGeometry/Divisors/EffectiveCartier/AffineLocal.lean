module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Chart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.PrincipalOfInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The affine-local characterization of an effective Cartier divisor

[Stacks, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS) — a closed subscheme `D ⊆ X` is an
effective Cartier divisor if and only if every point of `D` has an affine open neighbourhood
`U = Spec A` on which `U ∩ D = Spec (A / (f))` for a nonzerodivisor `f ∈ A` — is
`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal` in
`StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal`, which carries the
attribute.

This module exists only so that the chart lemmas of
`StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Chart` and
`.PrincipalOfInvertible` and that characterization are available together, which is what its
consumers import it for.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/
