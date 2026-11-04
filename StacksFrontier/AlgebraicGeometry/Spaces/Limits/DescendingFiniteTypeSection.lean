module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem

/-!
# Descending finite type algebraic spaces

Let `B = lim B_i` be the limit of a directed inverse system of Noetherian algebraic spaces with
affine transition morphisms. A quasi-separated finite type algebraic space `X` over `B` sits in
a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

with `W ⟶ B_i` of finite type and `X ⟶ B ×_{B_i} W` a closed immersion; such a diagram exhibits
`X` as the limit of the scheme-theoretic images `X_{i'}` of `X` in `B_{i'} ×_{B_i} W`, morphisms
descend to these systems, and flatness and smoothness descend as well.

## Implementation notes

The diagram is `AlgebraicGeometry.Space.GoodDiagram` (Tag 0CP8) over the system
`AlgebraicGeometry.Space.NoetherianLimitSystem` (Tag 0CP6). The section tag is registered on
these and on the declarations formalizing Tags 0CP9, 0CPA, 0CPC and 0CPD.

## References

* [Stacks Project, Tag 0CP5](https://stacks.math.columbia.edu/tag/0CP5)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
-/

@[expose] public section

add_to_stacks 0CP8 "the diagram: X ⟶ W over B ⟶ B_i, W ⟶ B_i of finite type and
  X ⟶ B ×_{B_i} W a closed immersion" AlgebraicGeometry.Space.GoodDiagram

add_to_stacks 0CP5 "the situation" AlgebraicGeometry.Space.NoetherianLimitSystem
add_to_stacks 0CP5 "the diagram" AlgebraicGeometry.Space.GoodDiagram
add_to_stacks 0CP5 "X is the limit of its scheme-theoretic images"
  AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone
add_to_stacks 0CP5 "morphisms descend to the systems of images"
  AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism
add_to_stacks 0CP5 "eventual uniqueness of the descended morphisms"
  AlgebraicGeometry.Space.GoodDiagram.eventually_eq_systemMorphism
add_to_stacks 0CP5 "flatness descends"
  AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback
add_to_stacks 0CP5 "smoothness descends"
  AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isSmooth
