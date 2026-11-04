module

public import StacksFrontier.CategoryTheory.FiberedCategory.RepresentableFibred
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms between categories fibred in groupoids represented by schemes

For the big fppf site over a scheme `S`, the morphisms between the categories fibred in
groupoids represented by two schemes `U`, `V` over `S`, taken modulo 2-isomorphism, are the
morphisms `U ⟶ V` over `S`; and more precisely every such morphism is induced by a
1-morphism which is unique up to a unique 2-isomorphism.

## Main results

* `CategoryTheory.Functor.twoIsoQuotientEquivHomOfRepresentableBy`: the bijection between
  1-morphisms modulo 2-isomorphism and morphisms of the representing objects.
* `CategoryTheory.Functor.exists_oneMorphism_inducing_hom`: the induced 1-morphism and its
  uniqueness up to a unique 2-isomorphism.

## Implementation notes

Both results already hold over an arbitrary base category, with no use of the fppf topology;
they are proved in that generality in
`StacksFrontier.CategoryTheory.FiberedCategory.RepresentableFibred` as Stacks 04SF. Specializing
the base category to `AlgebraicGeometry.BigFppfOver` gives the displayed equation of Stacks
04SR and its more precise formulation over `(Sch/S)_{fppf}`: the representing schemes are
objects of that slice category, so the morphisms on the right-hand side are morphisms over
`S`. No declaration is introduced here; the two existing ones are recorded as realizing the
tag.

## References

* [Stacks Project, Tag 04SR](https://stacks.math.columbia.edu/tag/04SR)
* [Stacks Project, Tag 04SF](https://stacks.math.columbia.edu/tag/04SF)
-/

add_to_stacks 04SR "equivalence of morphisms modulo two-isomorphism"
  CategoryTheory.Functor.twoIsoQuotientEquivHomOfRepresentableBy

add_to_stacks 04SR "induced morphism and uniqueness up to unique two-isomorphism"
  CategoryTheory.Functor.exists_oneMorphism_inducing_hom
