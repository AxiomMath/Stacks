module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The two canonical derived tensor bifunctors of a ringed site agree

Let `(C, O)` be a ringed site. The derived tensor product of Stacks 06YU is packaged twice in
this development: as `Stacks.SheafOfModules.DerivedTensorProduct`, indexed by the ringed site,
and as `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, indexed by the structure sheaf
alone. The two carry the same sixteen fields, but the structure-sheaf one hands its consumers
the construction `derivedTensorProductConstruction` and the site one the construction
`derivedTensorProductOfExact`, each opaque to the kernel (`irreducible_def`), so their
bifunctors are distinct terms. This file identifies them.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite`: a derived tensor product
  indexed by a ringed site, read as one indexed by its structure sheaf, with the same
  bifunctor.
* `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso`: the isomorphism
  `Stacks.SheafOfModules.derivedTensorProductFunctor X ≅
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O`.
* `AlgebraicGeometry.RingedSite.derivedTensorObjIso`: its value at a pair of objects.

## Implementation notes

The isomorphism factors through `CochainComplex.KFlatBifunctor.derivedBifunctor`, which
`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso` compares with the bifunctor of
an *arbitrary* structure-sheaf-indexed derived tensor product, using only its K-flat comparison
and the naturality of that comparison. Those two fields are shared verbatim by the
site-indexed structure, so `derivedTensorProductDatumOfSite` is a field-by-field reading and
the comparison is applied twice, with no new descent.

No declaration here carries a Stacks tag. Both sides are the derived tensor product of Stacks
06YU, which is proved and tagged at
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`; what this file adds is
bookkeeping internal to the development, not an assertion of the source.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u d

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules.{u, u, u} X)]

/-- A derived tensor product indexed by a ringed site is one indexed by its structure sheaf,
with the same bifunctor and the same comparisons with the total tensor complex. -/
def derivedTensorProductDatumOfSite
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X) :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} X.O where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  comparisonRight := T.comparisonRight
  comparisonRight_naturality := T.comparisonRight_naturality
  comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
  comparisonLeft := T.comparisonLeft
  comparisonLeft_naturality := T.comparisonLeft_naturality
  comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
  toTensor := T.toTensor
  toTensor_naturality := T.toTensor_naturality
  toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
  toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
  commShift₂ := T.commShift₂
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- **The canonical derived tensor bifunctor of a ringed site is the canonical derived tensor
bifunctor of its structure sheaf.** Both descend the total tensor complex of K-flat complexes
along the same localization, so each is isomorphic to
`CochainComplex.KFlatBifunctor.derivedBifunctor` and hence to the other. -/
def derivedTensorFunctorIso :
    Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X ≅
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O :=
  (Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
      (derivedTensorProductDatumOfSite X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X))).symm ≪≫
    Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)

/-- The comparison of the two canonical derived tensor bifunctors at a pair of objects of
`D(O)`. -/
def derivedTensorObjIso (A B : DerivedModules.{u, u, u, d} X) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj A).obj B ≅
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj A).obj B :=
  ((derivedTensorFunctorIso X).app A).app B

end AlgebraicGeometry.RingedSite

end
