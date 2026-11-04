module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphismFunctor

import StacksCore.Tactic.StacksAttribute

/-!
# The diagram defining relative morphisms

Let `S` be a scheme and `Z`, `X` schemes over `S`. For a scheme `T` over `S`, diagram (37.68.0.1)
pictures a morphism `b : T ×_S Z ⟶ T ×_S X` between the base changes of `Z` and `X` along
`T ⟶ S`, commuting with their projections to `T`. Such a `b` is a morphism
`prodOverBase Z T ⟶ (Over.star T).obj X` in the category of schemes over `T`, and the section goes
on to identify it with a morphism `T ×_S Z ⟶ X` over `S`, that is with an element of
`Mor_S(Z, X)(T) = (relativeHom Z X).obj (op T)`. That identification is
`AlgebraicGeometry.relativeHomObjEquivOverBase`, whose codomain is exactly the set of diagrams
(37.68.0.1); the tag is recorded on it.

## References

* [Stacks Project, Tag 0BL1](https://stacks.math.columbia.edu/tag/0BL1)
-/

@[expose] public section

add_to_stacks 0BL1 "the datum pictured by diagram (37.68.0.1), a morphism `b : T ×_S Z ⟶ T ×_S X` \
over `T`, identified with its description as a morphism `T ×_S Z ⟶ X` over `S`"
  AlgebraicGeometry.relativeHomObjEquivOverBase

end
