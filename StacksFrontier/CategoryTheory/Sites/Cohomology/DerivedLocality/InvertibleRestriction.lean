module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SliceDerivedTensorTransport
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComparisonWithTheDerivedTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat

/-!
# Invertibility in `D(O)` passes to restriction to a slice site

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction of sheaves of modules to
the localized site `C/U` carries an invertible object of `D(O)` to an invertible object of
`D(O|_U)`.

**No monoidal structure on the restriction functor is needed**: invertibility in a braided
monoidal category is a one-sided condition, so transporting it along a functor needs only a
*pairwise* comparison `F(A ⊗ B) ≅ F A ⊗ F B` together with `F(𝟙) ≅ 𝟙`, and that is
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided`. The pairwise
comparison here is
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso`, the value on arbitrary
objects of `D(O)` of the isomorphism of bifunctors

`(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U`,

and the unit comparison is `Stacks.SheafOfModules.FiniteTypeKernel.unitOverIso` — restriction
carries the structure sheaf to the structure sheaf of the slice — moved into the derived
categories by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

## Main definitions

* `Stacks.Cohomology.SliceInvertible.restrictionUnitIso` and
  `Stacks.Cohomology.SliceInvertible.derivedRestrictionUnitIso`: the restriction of the
  structure sheaf is the structure sheaf of the slice, before and after the degree-zero
  inclusion into the derived categories.

## Main results

* `Stacks.Cohomology.SliceInvertible.isInvertible_restriction_of_isInvertible`: the transport,
  with the two monoidal structures and their comparisons as explicit arguments.
* `Stacks.Cohomology.SliceInvertible.isInvertible_restriction`: the same statement at the
  monoidal structure of [Stacks, Tag 0FPT] on both sides.

## Reading it on a ringed space

Read on a ringed space the restriction functor is `SheafOfModules.overFunctor` — the spelling
`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor` and
`Stacks.SheafOfModules.isInvertible_of_isIso_restrict_derivedUnitEvaluation` are phrased in:
`Stacks.DerivedTensor.ExtensionByZero.restriction (Stacks.SheafOfModules.ringedSite Rc) V` is
that functor, so `isInvertible_restriction (Stacks.SheafOfModules.ringedSite Rc) V` is the
statement there.

## Implementation notes

The two monoidal structures are arguments rather than instances, exactly as in
`Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk_of_isInvertible`: each of
`D(O)` and `D(O|_U)` carries several inhabitants of "the" derived tensor product — the
localized one of [Stacks, Tag 0FPT], the re-seated one of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, and on a ringed space the
re-seated `Stacks.SheafOfModules.derivedMonoidalStructure` — which are isomorphic but not
equal. Each supplies a pairwise tensor comparison and a unit identification, so the general
form applies to all of them.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe d u

namespace Stacks.Cohomology.SliceInvertible

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor X.O).Additive]
  [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- **Restriction to a slice carries the structure sheaf to the structure sheaf of the slice**,
on the nose: this is `Stacks.SheafOfModules.FiniteTypeKernel.unitOverIso`, read at the
spellings a ringed site uses. -/
def restrictionUnitIso :
    (restriction X U).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U)) :=
  (Stacks.SheafOfModules.FiniteTypeKernel.unitOverIso
    (R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) U).symm

/-- **The restriction of the structure sheaf in degree zero is the structure sheaf of the slice
in degree zero.** This is `Stacks.Cohomology.SliceInvertible.restrictionUnitIso` moved through
the degree-zero inclusion by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def derivedRestrictionUnitIso :
    (restriction X U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Modules X.O) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))) ≅
      (DerivedCategory.singleFunctor (Modules (X.O.over U)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U))) :=
  ((restriction X U).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (Modules (X.O.over U)) 0).mapIso (restrictionUnitIso X U)

/-- **Restriction to a slice site carries an invertible object of `D(O)` to an invertible
object of `D(O|_U)`.**

The two monoidal structures are explicit arguments, each with the two data that identify it:
`cmpX` and `cmpU` compare its tensor product, pairwise, with the derived tensor bifunctor of
[Stacks, Tag 06YU], and `unitX`, `unitU` identify its unit with the structure sheaf in degree
zero.

The proof uses the comparison
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso` at a single pair of
objects and nothing else: invertibility in a braided category is one-sided, so
`CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided` asks for no
coherence of the comparison. -/
theorem isInvertible_restriction_of_isInvertible
    (mX : MonoidalCategory (DerivedCategory (Modules X.O)))
    (mU : MonoidalCategory (DerivedCategory (Modules (X.O.over U))))
    (bU : letI := mU; BraidedCategory (DerivedCategory (Modules (X.O.over U))))
    (cmpX : letI := mX; ∀ A B : DerivedCategory (Modules X.O),
      A ⊗ B ≅ ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (sheafTensor X.O)).obj A).obj B)
    (unitX : letI := mX; 𝟙_ (DerivedCategory (Modules X.O)) ≅
      (DerivedCategory.singleFunctor (Modules X.O) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
    (cmpU : letI := mU; ∀ A B : DerivedCategory (Modules (X.O.over U)),
      A ⊗ B ≅ ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (sheafTensor (X.O.over U))).obj A).obj B)
    (unitU : letI := mU; 𝟙_ (DerivedCategory (Modules (X.O.over U))) ≅
      (DerivedCategory.singleFunctor (Modules (X.O.over U)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U))))
    (K : DerivedCategory (Modules X.O))
    (hK : letI := mX; CategoryTheory.MonoidalCategory.IsInvertible K) :
    letI := mU
    CategoryTheory.MonoidalCategory.IsInvertible
      ((restriction X U).mapDerivedCategory.obj K) :=
  let := mX
  let := mU
  let := bU
  CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided
    (restriction X U).mapDerivedCategory
    (fun A B => (restriction X U).mapDerivedCategory.mapIso (cmpX A B) ≪≫
      Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso X U A B ≪≫
      (cmpU _ _).symm)
    ((restriction X U).mapDerivedCategory.mapIso unitX ≪≫
      derivedRestrictionUnitIso X U ≪≫ unitU.symm) hK

omit [(sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).Additive]
  [∀ M : Modules X.O, ((sheafTensor X.O : Modules X.O ⥤ Modules X.O ⥤ Modules X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U) :
    Modules (X.O.over U) ⥤ Modules (X.O.over U) ⥤ Modules (X.O.over U)).Additive]
  [∀ M : Modules (X.O.over U), ((sheafTensor (X.O.over U) :
    Modules (X.O.over U) ⥤ Modules (X.O.over U) ⥤ Modules (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)] in
/-- **Restriction to a slice site carries an invertible object of `D(O)` to an invertible object
of `D(O|_U)`**, at the symmetric monoidal structure of [Stacks, Tag 0FPT] on both sides. -/
theorem isInvertible_restriction (K : DerivedCategory (Modules X.O))
    (hK : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
      CategoryTheory.MonoidalCategory.IsInvertible K) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U)
    CategoryTheory.MonoidalCategory.IsInvertible
      ((restriction X U).mapDerivedCategory.obj K) :=
  isInvertible_restriction_of_isInvertible X U
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U))
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric (X.O.over U)).toBraidedCategory
    (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso
      X.O).app A).app B)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)
    (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso
      (X.O.over U)).app A).app B)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (X.O.over U)) K hK

end Stacks.Cohomology.SliceInvertible

end
