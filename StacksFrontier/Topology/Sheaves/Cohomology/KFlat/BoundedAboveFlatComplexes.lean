module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded above complex of flat modules on a ringed space is K-flat

Let `(X, O_X)` be a ringed space. A bounded above cochain complex of flat `O_X`-modules is
K-flat, i.e. tensoring it with an acyclic complex gives an acyclic total complex.

This is the ringed-space case of the corresponding statement for a ringed site, Tag 06YQ,
which is proved as `Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`. A ringed space is
a topological space `X` together with a sheaf of commutative rings on the site of its open
subsets: `TopCat.Sheaf CommRingCat X` is by definition
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat`, and a sheaf of
`O_X`-modules is a `SheafOfModules` over the underlying sheaf of rings of that site. So the
site-level theorem applies verbatim, with no extra hypothesis and no change of universes:
the site of opens of `X : TopCat.{u}` is `Opens X : Type u` with `Category.{u}`, so Tag
06YQ's module universe `max u v w` is `u`, which is the universe `O_X`-modules live in.
This file therefore records Tag 06YD on that theorem rather than restating it.

## Main results

No new results are proved here. Tag 06YD is registered on
`Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`.

## Implementation notes

The two neighbouring tags of this family are registered the same way, on statements for a
general ringed site: Tag 06Y9, the definition of K-flatness, is
`Stacks.SheafOfModules.IsKFlat`, and Tag 06YE, stability under sequential colimits, is
`Stacks.SheafOfModules.kFlat_colimit`. In particular the notion of
K-flatness named in the conclusion of Tag 06YD is the very constant that already carries
Tag 06Y9, so no second notion is introduced by registering Tag 06YD at site generality.

## References

* [Stacks Project, Tag 06YD](https://stacks.math.columbia.edu/tag/06YD)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

add_to_stacks 06YD "ringed space case of the ringed site statement"
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat
