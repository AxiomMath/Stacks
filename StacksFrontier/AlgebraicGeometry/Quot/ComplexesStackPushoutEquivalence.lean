module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPushoutsProved

/-!
# `Complexes_{X/B}` turns pushouts along finite order thickenings into fibre products

In Situation 0DLE (`f : X ⟶ B` proper, flat and of finite presentation), let
`Y' = Y ⨿_Z Z'` be a pushout of schemes over `S` along a finite order thickening `Z ⟶ Z'` and an
affine morphism `Z ⟶ Y`. Then the functor on fibre categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence: [Stacks Project, Tag 0DLK]. This is
`AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_proved`.

## References

* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public section

add_to_stacks 0DLK AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_proved

end
