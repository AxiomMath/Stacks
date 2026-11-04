module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCoveringAxioms
public import StacksFrontier.Topology.Compact.LocallyQuasiCompactHausdorffCat
public import StacksFrontier.Topology.Separation.FibreProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact coverings and quasi-compact fibre products in `LC`

`LC` is the category of Hausdorff, locally quasi-compact topological spaces
(`Stacks.Topology.LocallyQuasiCompactHausdorff`). This file records two facts about it.

A family of maps with fixed target is a *qc covering* when, near every point of the target,
finitely many images of quasi-compact subsets of the sources cover a neighbourhood. That is the
predicate `IsQcCovering`, which is Stacks 09X0; it is
stated for arbitrary topological spaces and maps, since neither continuity nor the separation
and local quasi-compactness hypotheses enter the covering condition itself, and specialising its
spaces and maps to objects and morphisms of `LC` recovers the source's definition for `LC`.

Separately, the fibre product of two quasi-compact objects of `LC` is quasi-compact: it is a
closed subset of the product, which is quasi-compact by Tychonoff. This is the last clause of
Stacks 09WZ; the other three — that `LC` has fibre products, a final object and hence all
finite limits — are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LocallyQuasiCompact/FiniteLimits.lean`.

## Main results

* Stacks 09X0 is realised by `IsQcCovering`.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.isCompact_fibreProduct`: the subspace
  `fibreProduct f g` of `X × Y` cut out by two morphisms of `LC` out of quasi-compact objects
  is quasi-compact.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.pullbackHomeoFibreProduct`: the categorical
  fibre product of `LC` is homeomorphic to that subspace.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.compactSpace_pullback`: hence the categorical
  fibre product `X ×_Z Y` of `LC` is quasi-compact. This is the clause of Stacks 09WZ.

## Implementation notes

The subspace is the existing subset `fibreProduct` of the product space, not a new
construction; `fibreProduct_isClosed` is Stacks 08ZH, and the target of the two morphisms being
Hausdorff is what makes it closed. Hausdorffness of the target is not an added hypothesis: it is
part of being an object of `LC`. Quasi-compactness of a subspace is expressed as `IsCompact` of
the underlying subset, and the morphisms of the full subcategory are used as their underlying
continuous maps.

The clause is carried by `compactSpace_pullback`, stated about the chosen categorical
`Limits.pullback` of `LC`, so that it speaks of the same object as the other three clauses of
the tag. `pullbackHomeoFibreProduct` identifies that object with `fibreProduct f g`: the
inclusion of `LC` into `TopCat` creates fibre products, hence preserves them, and
`TopCat.pullbackIsoProdSubtype` identifies the topological fibre product with the subspace.
`isCompact_fibreProduct` is the underlying topological fact and is left untagged.

## References

* [Stacks Project, Tag 09X0](https://stacks.math.columbia.edu/tag/09X0)
* [Stacks Project, Tag 09WZ](https://stacks.math.columbia.edu/tag/09WZ)
* [Stacks Project, Tag 08ZH](https://stacks.math.columbia.edu/tag/08ZH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

-- Tag 09X0: a family of maps with fixed target is a quasi-compact covering.
add_to_stacks 09X0 "qc coverings of locally quasi-compact Hausdorff spaces" IsQcCovering

namespace Stacks.Topology.LocallyQuasiCompactHausdorff

universe u

/-- Given morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` of Hausdorff, locally quasi-compact spaces
with `X` and `Y` quasi-compact, the subspace `fibreProduct f g` of `X × Y` is quasi-compact:
it is closed in `X × Y` because `Z` is Hausdorff, and `X × Y` is quasi-compact. -/
theorem isCompact_fibreProduct {X Y Z : LocallyQuasiCompactHausdorff.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [CompactSpace X] [CompactSpace Y] : IsCompact (fibreProduct f g) :=
  (fibreProduct_isClosed (ConcreteCategory.hom f.hom).continuous
    (ConcreteCategory.hom g.hom).continuous).isCompact

/-- The fibre product of `f : X ⟶ Z` and `g : Y ⟶ Z` in `LC` is homeomorphic to the subspace
`fibreProduct f g` of `X × Y`. The inclusion of `LC` into `TopCat` creates fibre products,
hence preserves them, and the fibre product in `TopCat` is that subspace. -/
noncomputable def pullbackHomeoFibreProduct {X Y Z : LocallyQuasiCompactHausdorff.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g : LocallyQuasiCompactHausdorff.{u}) ≃ₜ fibreProduct f g :=
  TopCat.homeoOfIso
    (PreservesPullback.iso locallyQuasiCompactHausdorffToTop f g ≪≫
      TopCat.pullbackIsoProdSubtype _ _)

/-- **Stacks 09WZ, the quasi-compactness clause.** Given morphisms `f : X ⟶ Z` and
`g : Y ⟶ Z` of Hausdorff, locally quasi-compact spaces with `X` and `Y` quasi-compact, the
fibre product `X ×_Z Y` in `LC` is quasi-compact. -/
@[stacks 09WZ "quasi_compact"]
theorem compactSpace_pullback {X Y Z : LocallyQuasiCompactHausdorff.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [CompactSpace X] [CompactSpace Y] :
    CompactSpace (pullback f g : LocallyQuasiCompactHausdorff.{u}) :=
  have : CompactSpace (fibreProduct f g) :=
    isCompact_iff_compactSpace.mp (isCompact_fibreProduct f g)
  (pullbackHomeoFibreProduct f g).symm.compactSpace

end Stacks.Topology.LocallyQuasiCompactHausdorff
