module

public import StacksFrontier.AlgebraicGeometry.Pushout.InducedMorphism

/-!
# A morphism between pushouts of schemes

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions and let `f : X' ⟶ X` and `g : Y' ⟶ Y` be
morphisms whose inverse images of `Z` are identified over `Z` by an isomorphism
`X' ×_X Z ≅ Y' ×_Y Z`.  Gluing `X'` and `Y'` along that common inverse image gives a pushout
mapping canonically to the pushout of `X` and `Y` along `Z`.

That situation and the morphism it induces are developed in
`StacksFrontier.AlgebraicGeometry.Pushout.InducedMorphism`, which this file re-exports:
`AlgebraicGeometry.CompatiblePushoutMorphismSituation` together with its
`AlgebraicGeometry.CompatiblePushoutMorphismSituation.sourcePushout` and
`AlgebraicGeometry.CompatiblePushoutMorphismSituation.induced`.  There the existence of the
two pushouts is supplied by the instance
`AlgebraicGeometry.hasPushout_of_isClosedImmersion` instead of being hypothesised, since both
legs of each span are closed immersions.

## References

* [Stacks Project, Tag 0CYY](https://stacks.math.columbia.edu/tag/0CYY)
-/
