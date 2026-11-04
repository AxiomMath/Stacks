module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.Equivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent objects on the big affine site of an algebraic space

For an algebraic space `X` over a scheme `S`, the category `QC((Aff/X), 𝒪)` of quasi-coherent
objects in the derived category of the big affine site is canonically equivalent to
`D_QCoh(𝒪_X)`. Stacks 0H07 states this equivalence and defers its proof to Stacks 0H0K.

This file registers the tag on that proof. It declares nothing of its own.

## References

* [Stacks Project, Tag 0H07](https://stacks.math.columbia.edu/tag/0H07)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
-/

add_to_stacks 0H07 "the equivalence QC((Aff/X), 𝒪) ≌ D_QCoh(𝒪_X), on the proof of Stacks 0H0K"
  AlgebraicGeometry.Stack.representableQuasiCoherentDerivedEquivalence
