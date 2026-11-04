module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalComparisonBraided
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity

/-!
# The commutativity constraint on a ringed space, through the K-flat comparison

`Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding` is the commutativity constraint
of Stacks 0FPB on `D(𝒪_Z)` for a ringed space `Z`, read on the uncurried bifunctor the relative
cup product of Stacks 0B68 is stated over — that bifunctor being the derived tensor product of
Stacks 06YU on the nose.  This file records that it is the Koszul symmetry of complexes, read
through the K-flat comparison of that tensor product:

```
Q(K) ⊗^L Q(L) ------> Q(Tot(K ⊗_{𝒪_Z} L))
      |                        |
      | ψ                      | Q(Koszul)
      v                        v
Q(L) ⊗^L Q(K) ------> Q(Tot(L ⊗_{𝒪_Z} K))
```

It is the ringed-space reading of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_koszulBraiding`, which is the same
statement for a ringed site; `derivedBraiding` is the braiding of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric` by definition, so the two
are the same proposition and nothing is re-proved.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding_comp_canonicalComparison`: the
  square above.

## Implementation notes

The monoidal structure of `Mod 𝒪_Z` is supplied by `letI` rather than by an `attribute [local
instance]`.  `SheafOfModules.monoidalCategorySheafTensor` is stated at `SheafOfModules.{max u
v}` for a site `C : Type u` with `Category.{v} C`, and over the opens of a topological space
instance resolution has no way to split the single universe of `Mod 𝒪_Z` into that `max`; given
the term, it has nothing to split.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.DerivedRelativeCupProduct

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The commutativity constraint of Stacks 0FPB on a ringed space is the Koszul symmetry of
complexes**, read through the K-flat comparison of the derived tensor product of Stacks 06YU:
for K-flat complexes `K` and `L` of `𝒪_Z`-modules, the constraint followed by the comparison at
`(L, K)` is the comparison at `(K, L)` followed by the image of
`CochainComplex.koszulBraiding`. -/
theorem derivedBraiding_comp_canonicalComparison (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K L : Complexes Z.sheaf} (hK : KFlat Z.sheaf K) (hL : KFlat Z.sheaf L) :
    letI := SheafOfModules.monoidalCategorySheafTensor Z.sheaf
    letI := SheafOfModules.symmetricCategorySheafTensor Z.sheaf
    letI := SheafOfModules.monoidalPreadditiveSheafTensor Z.sheaf
    letI := SheafOfModules.monoidalClosedSheafTensor Z.sheaf
    derivedBraiding Z (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        (canonicalComparison Z.sheaf L K hL hK).hom =
      (canonicalComparison Z.sheaf K L hK hL).hom ≫
        DerivedCategory.Q.map (CochainComplex.koszulBraiding K L).hom :=
  canonicalComparison_koszulBraiding Z.sheaf hK hL

end Stacks.Cohomology.DerivedRelativeCupProduct

end
