module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts

/-!
# Surjectivity of the chart homomorphisms of a closed immersion

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a closed immersion
of fppf sheaves over `S`.  The condition
`AlgebraicGeometry.FormalSpace.HasSurjectiveOnPullbackCharts` asks that on every affine
representable étale chart `V ⟶ Y` of the target and every presentation of a fibre product of
`f` along it by adic Noetherian rings, the induced continuous homomorphism of presenting rings
be surjective.  It is the single clause of Stacks 0AQI which the proof of Stacks 0GD5 consumes.

That it holds for a closed immersion, carrying nothing, is
`AlgebraicGeometry.FormalSpace.hasSurjectiveOnPullbackCharts_of_isClosedImmersion`.  It lives in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts`, upstream of the
Stacks 0GD5 statement there, which uses it; this module retains nothing of its own.

No hypothesis `AlgebraicGeometry.FormalSpace.IsTautOfRepresentableFormalSpectrumMap` is needed,
because the implication (1) ⟹ (3) of **Stacks 0AN5** is available
in the shape the derivation needs it,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
and the two set-theoretic conditions it carries are free on chart rings, which are adic and
carry quotient systems.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
-/
