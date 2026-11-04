module

public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism.Evaluation
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism.FormalObjectEquivalence
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism.RepresentedRestriction

/-!
# Morphisms from a represented functor and formal objects (Stacks 06SK)

For a complete local algebra `R`, morphisms over the Artinian base from the restriction of
the functor represented by `R` to a category cofibered in groupoids are equivalent to formal
objects over `R`. The development is split into `RepresentableMorphism.Evaluation` (evaluation
at the identity point, 2-Yoneda, and the canonical Artinian quotient points),
`RepresentableMorphism.RepresentedRestriction` (the restricted represented functor as the
strict restriction of its category of elements) and
`RepresentableMorphism.FormalObjectEquivalence` (the equivalence, **Stacks 06SK**).
-/
