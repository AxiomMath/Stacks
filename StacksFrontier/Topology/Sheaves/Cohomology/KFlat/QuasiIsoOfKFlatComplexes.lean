module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring a quasi-isomorphism of K-flat complexes on a ringed space

Let `(X, O_X)` be a ringed space and let `α : P^• ⟶ Q^•` be a quasi-isomorphism of K-flat
complexes of `O_X`-modules. Then for every complex `F^•` of `O_X`-modules the induced map
`Tot(id_{F^•} ⊗ α) : Tot(F^• ⊗_{O_X} P^•) ⟶ Tot(F^• ⊗_{O_X} Q^•)` is again a
quasi-isomorphism.

This is the ringed-space case of the ringed-site statement, Tag 06YT, which is proved as
`Stacks.SheafOfModules.quasiIso_mapBifunctorMap_id_of_kFlat_right` and, in the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling, as
`Stacks.SheafOfModules.quasiIso_tensorComplex_obj_map_of_kFlat`. A ringed space is a
topological space `X` together with a sheaf of commutative rings on the site of its open
subsets, and a sheaf of `O_X`-modules is a `SheafOfModules` over the underlying sheaf of
rings of that site; the site of opens of `X : TopCat.{u}` is `Opens X : Type u` with
`Category.{u}`, so the site statement applies verbatim, at the universe in which
`O_X`-modules live and with no extra hypothesis. This file therefore records Tag 06YG on
those two theorems rather than restating them.

The notion of K-flatness appearing in both hypothesis and conclusion is
`Stacks.SheafOfModules.IsKFlat`, the very constant that carries Tag 06Y9, so registering Tag
06YG at site generality introduces no second notion of K-flatness and no second tensor
product.

## Main results

No new results are proved here. Tag 06YG is registered on
`Stacks.SheafOfModules.quasiIso_mapBifunctorMap_id_of_kFlat_right` and on
`Stacks.SheafOfModules.quasiIso_tensorComplex_obj_map_of_kFlat`.

## References

* [Stacks Project, Tag 06YG](https://stacks.math.columbia.edu/tag/06YG)
* [Stacks Project, Tag 06YT](https://stacks.math.columbia.edu/tag/06YT)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

add_to_stacks 06YG "ringed space case of the ringed site statement"
  Stacks.SheafOfModules.quasiIso_mapBifunctorMap_id_of_kFlat_right

add_to_stacks 06YG "ringed space case, tensorComplex spelling"
  Stacks.SheafOfModules.quasiIso_tensorComplex_obj_map_of_kFlat
