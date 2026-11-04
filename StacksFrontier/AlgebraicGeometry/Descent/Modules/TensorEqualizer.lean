module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer.CharacterDuality
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer.Comparison
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer.Equalizer

/-!
# Tensoring the equalizer of a module descent datum

For a universally injective homomorphism of commutative rings, the equalizer defining the
pushforward of a module descent datum remains an equalizer after tensoring with the target
ring.

## Main definitions

* `ModuleCat.tensorPushforwardComparison` is the first arrow of the tensorized equalizer
  diagram, under the canonical interchange of tensor factors.
* `ModuleCat.unitBaseChangeMap` is the insertion `p ↦ 1 ⊗ p`.

## Main results

* `ModuleCat.tensorPushforwardComparison_tmul` identifies the first arrow with the pullback of
  the descent transition.
* `ModuleCat.tensorPushforwardComparison_condition` says that the first arrow equalizes the two
  canonical pullback arrows.
* `ModuleCat.tensorPushforward_isEqualizer` gives the universal property of the displayed
  diagram of `A`-modules.

## Implementation notes

The first object is written `A ⊗[R] f₊(M, θ)` rather than `f₊(M, θ) ⊗[R] A`, using the
canonical tensor symmetry. Its map is the `A`-linear lift of the subtype inclusion; the
comparison formula shows that it is precisely the transition-derived arrow in the source. The
other two arrows are the canonical `A`-linear pullbacks of the transition and the unit
insertion. The conclusion is an `IsLimit` of the fork of the displayed `A`-linear maps, so it
records the categorical equalizer rather than only a pointwise criterion. The scalar in the
comparison formula acts on the module before applying the transition: invariance and
first-factor linearity give `θ((a • m) ⊗ 1) = a ⊗ m`.

The rings and the module have independent universes. Universal injectivity is expressed with
test modules in the source ring's universe; when the rings share a universe this is the
predicate `Algebra.UniversallyInjective`.

The equalizer is produced by dualizing: character duality turns the split equalizer of the
descent diagram into a split coequalizer, universal injectivity spreads a splitting over the
tensor factors functorially, and a split coequalizer of character modules reflects back to a
limit fork of the original modules.

## References

* [Stacks Project, Tag 08X7](https://stacks.math.columbia.edu/tag/08X7)
-/
