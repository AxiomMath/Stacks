module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion

/-!
# Universally injective étale morphisms are open immersions

An étale morphism of schemes which is universally injective is an open immersion.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective` (in
  `StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion`, re-exported here):
  a universally injective étale morphism of schemes is an open immersion.

## References

* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
-/

@[expose] public section
