module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion

/-!
# Stacks 05ZR, unconditionally

A thickening of algebraic spaces whose source is a scheme has a scheme as target (Stacks 05ZR).
Both forms, the subspace form of Stacks 05ZK and the morphism form, are proved without
hypotheses in `StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion`
from the closed-immersion form of Stacks 07VV.  This file attaches the tag to them.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

add_to_stacks 05ZR AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable

add_to_stacks 05ZR "the morphism form"
  AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable

end
