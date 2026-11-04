module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThree
import StacksCore.Tactic.StacksAttribute

/-!
# Two out of three for K-flat complexes on a ringed space

Let `(X, O_X)` be a ringed space. K-flatness of complexes of `O_X`-modules satisfies
two-out-of-three in both of the situations the source records:

* in a distinguished triangle `(K_1^•, K_2^•, K_3^•)` of `K(Mod(O_X))`, if two of the three
  vertices are K-flat then so is the third (Tag 079S);
* in a short exact sequence `0 → K_1^• → K_2^• → K_3^• → 0` of complexes whose third term has
  flat terms, if two of the three complexes are K-flat then so is the third (Tag 0G6U).

Both are the ringed-space case of the corresponding ringed-site statement — Tag 07A3 for the
triangle and Tag 0G7B for the short exact sequence — which are proved as
`Stacks.SheafOfModules.kFlat_of_second_third` and its two siblings, and as
`Stacks.SheafOfModules.isKFlat_two_out_of_three`. A ringed space is a topological space `X`
together with a sheaf of commutative rings on the site of its open subsets, and a sheaf of
`O_X`-modules is a `SheafOfModules` over the underlying sheaf of rings of that site; since the
site of opens of `X : TopCat.{u}` is `Opens X : Type u` with `Category.{u}`, both site
statements apply verbatim, with no extra hypothesis and at the universe in which
`O_X`-modules live. This file therefore records the two space-level tags on them rather than
restating them.

K-flatness in the conclusions is `Stacks.SheafOfModules.IsKFlat`, the constant carrying Tag
06Y9 — for Tag 079S through `CochainComplex.KFlatBifunctor.KFlat` at the canonical tensor
bifunctor, which unfolds to it — so no second notion of K-flatness is introduced here.

## Main results

No new results are proved here. Tag 079S is registered on the three implications
`Stacks.SheafOfModules.kFlat_of_second_third`, `kFlat_of_first_third` and
`kFlat_of_first_second`, which together make up its assertion, and Tag 0G6U on
`Stacks.SheafOfModules.isKFlat_two_out_of_three`, which asserts all three of its implications
at once.

## References

* [Stacks Project, Tag 079S](https://stacks.math.columbia.edu/tag/079S)
* [Stacks Project, Tag 0G6U](https://stacks.math.columbia.edu/tag/0G6U)
* [Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
* [Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

add_to_stacks 079S "ringed space case of the ringed site statement, first vertex"
  Stacks.SheafOfModules.kFlat_of_second_third

add_to_stacks 079S "ringed space case of the ringed site statement, second vertex"
  Stacks.SheafOfModules.kFlat_of_first_third

add_to_stacks 079S "ringed space case of the ringed site statement, third vertex"
  Stacks.SheafOfModules.kFlat_of_first_second

add_to_stacks 0G6U "ringed space case of the ringed site statement"
  Stacks.SheafOfModules.isKFlat_two_out_of_three
