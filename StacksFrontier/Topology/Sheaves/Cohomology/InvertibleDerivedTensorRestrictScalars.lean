module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsInvertibility
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorMonoidal

/-!
# Reading an `𝒪_n`-module as an `𝒪_X`-module commutes with the tensor product

Let `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` be a locally finite direct product decomposition of the structure sheaf
of a ringed space (`Stacks.Cohomology.InvertibleDerived.ProductDecomposition`).  For two sheaves
of `𝒪_n`-modules `A` and `B`,

`(A as an 𝒪_X-module) ⊗_{𝒪_X} (B as an 𝒪_X-module) ≅ (A ⊗_{𝒪_n} B) as an 𝒪_X-module`,

in `Mod(O_X)`.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.tensorObjIsoToOXMod`: the
  identification above.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.tensorObjIsoToOXModUnit`: if
  `A ⊗_{𝒪_n} B` is the unit module of the factor, then the tensor product over `𝒪_X` of the two
  modules read as `𝒪_X`-modules is `𝒪_n` read as an `𝒪_X`-module.

## Main results

* `ProductDecomposition.exists_derivedTensor_iso_of_isInvertibleModule_of_isFlat`: an invertible
  `𝒪_n`-module `H` which is flat as an `𝒪_X`-module has a partner `H'` whose derived tensor product
  with `H` over `𝒪_X`, both read as `𝒪_X`-modules, is `𝒪_n` read as an `𝒪_X`-module.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u d

namespace Stacks.Cohomology.InvertibleDerived.ProductDecomposition

open Stacks.SheafOfModules.RingSheafProductFactor

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **The product presentation of `𝒪_X` underlying a locally finite product decomposition**: the
decomposition's identification of `𝒪_X` with `∏ 𝒪_n`, read as a product presentation.  Its `n`-th
projection is `ProductDecomposition.proj n`. -/
public def productPresentation (D : ProductDecomposition X) :
    ProductPresentation X.sheaf D.factor :=
  ProductPresentation.ofIso D.iso

/-- `ProductDecomposition.toOXMod` is restriction of scalars along the projection of
`ProductDecomposition.productPresentation`, by definition. -/
public theorem toOXMod_eq_restrictScalars_projRing (D : ProductDecomposition X) (n : ℤ) :
    D.toOXMod n =
      SheafOfModules.restrictScalars (projRing D.productPresentation n) :=
  rfl

/-- **Reading `𝒪_n`-modules as `𝒪_X`-modules commutes with the tensor product**:

`(A as an 𝒪_X-module) ⊗_{𝒪_X} (B as an 𝒪_X-module) ≅ (A ⊗_{𝒪_n} B) as an 𝒪_X-module`. -/
public def tensorObjIsoToOXMod (D : ProductDecomposition X) (n : ℤ)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    letI := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
    ((D.toOXMod n).obj A ⊗ (D.toOXMod n).obj B) ≅ (D.toOXMod n).obj (A ⊗ B) :=
  tensorObjIsoRestrictScalars₂ D.productPresentation n A B

/-- If two `𝒪_n`-modules have the unit module of `𝒪_n` as their tensor product, then their tensor
product over `𝒪_X`, both read as `𝒪_X`-modules, is `𝒪_n` read as an `𝒪_X`-module. -/
public def tensorObjIsoToOXModUnit (D : ProductDecomposition X) (n : ℤ)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (e : letI := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
      (A ⊗ B) ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    ((D.toOXMod n).obj A ⊗ (D.toOXMod n).obj B) ≅
      (D.toOXMod n).obj (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) := by
  letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  letI := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
  exact tensorObjIsoToOXMod D n A B ≪≫ (D.toOXMod n).mapIso e

/-- Let `D` be a locally finite product decomposition `𝒪_X = ∏ 𝒪_n` and `H` an invertible
`𝒪_n`-module which is flat as an `𝒪_X`-module. Then there is an `𝒪_n`-module `H'` such that, in
`D(𝒪_X)`, the derived tensor product of `H` and `H'`, both read as `𝒪_X`-modules, is isomorphic to
`𝒪_n` read as an `𝒪_X`-module. -/
public theorem exists_derivedTensor_iso_of_isInvertibleModule_of_isFlat
    (D : ProductDecomposition X)
    [HasDerivedCategory.{d} (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf)] (n : ℤ)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((D.toOXMod n).obj H)) :
    ∃ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)),
      letI := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
      Nonempty (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor
          (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) 0).obj ((D.toOXMod n).obj H))
        ((DerivedCategory.singleFunctor
          (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) 0).obj ((D.toOXMod n).obj H')) ≅
          (DerivedCategory.singleFunctor
            (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) 0).obj ((D.toOXMod n).obj
              (SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) := by
  let := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  let := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
  obtain ⟨H', ⟨e⟩⟩ :=
    exists_tensorObj_iso_factorModule_of_isInvertibleModule D.productPresentation n H hH
  exact ⟨H', ⟨MonoidalDerived.derivedTensorSingleIso.{u, d} X _ _ hflat ≪≫
    (DerivedCategory.singleFunctor (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) 0).mapIso e⟩⟩

end Stacks.Cohomology.InvertibleDerived.ProductDecomposition

end
