module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSigmaDistribution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSingleTensorIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorKFlatOneSided

/-!
# Orthogonality of the factors of a product decomposition of the structure sheaf

Let `(C, O)` be a ringed site with a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of its structure sheaf
(`AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`), and read
`O_n`-modules as `O`-modules by restriction of scalars along the projections. For `n ≠ m`, an
`O_n`-module and an `O_m`-module have vanishing tensor product over `O`, and vanishing derived
tensor product in `D(O)` when placed in degree zero. Two `O_n`-modules whose tensor product over
`O_n` is `O_n` have tensor product `O_n` over `O`.

All declarations are in the namespace `AlgebraicGeometry.RingedSite.InvertibleDerived`.

## Main definitions

* `ProductDecomposition.tensorObjIsoToOMod`: reading `O_n`-modules as `O`-modules commutes with
  the tensor product.
* `ProductDecomposition.tensorObjIsoToOModUnit`: if two `O_n`-modules have tensor product `O_n`,
  their tensor product over `O` is `O_n`.

## Main results

* `ProductDecomposition.isFlat_toOMod_unit`: each factor, read as an `O`-module, is flat.
* `ProductDecomposition.isZero_tensor_toOMod`: for `n ≠ m`, an `O_n`-module and an `O_m`-module
  have vanishing tensor product over `O`.
* `ProductDecomposition.nonempty_retract_tensor_toOMod`: an `O_n`-module is a retract of
  `O_n ⊗_O` itself in `Mod(O)`.
* `ProductDecomposition.isZero_derivedTensor_toOMod_of_ne`: for `n ≠ m`, an `O_n`-module and an
  `O_m`-module placed in degree zero have vanishing derived tensor product in `D(O)`.

## Implementation notes

The vanishing of the tensor product of two modules in degree zero needs no flatness; flatness
enters only through the one-sided K-flat comparison of the derived and the underived tensor
product, which needs one K-flat argument. The derived vanishing is first proved with the module on
one side flat; that module is then the factor `O_m`, which is flat as a retract of `O`, and an
arbitrary `O_m`-module `L'` is recovered as a retract of `O_m ⊗^𝐋 L'`.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT): the derived tensor
  product on `D(O)`.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA): the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K): invertible modules.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

namespace ProductDecomposition

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheaves of `O`-modules have binary biproducts, as a preadditive category with binary
products. -/
local instance hasBinaryBiproductsModules :
    HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-! ### The factor is flat -/

/-- Each factor `O_n` of a product decomposition, read as an `O`-module, is flat over `O`. -/
theorem isFlat_toOMod_unit (D : ProductDecomposition X) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) := by
  obtain ⟨ret⟩ := D.nonempty_retract_toOMod_unit n
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.O ret.i ret.r ret.retract
    (Stacks.SheafOfModules.isFlat_unit X.O)

/-! ### The orthogonality at the level of sheaves -/

/-- **The orthogonality of the factors, for arbitrary modules over them.**  For `n ≠ m`, an
`O_n`-module `L` and an `O_m`-module `L'`, each read as an `O`-module by restriction of scalars
along the projections of a product decomposition, have vanishing tensor product over `O`. -/
theorem isZero_tensor_toOMod (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.O
    IsZero (MonoidalCategory.tensorObj ((D.toOMod n).obj L) ((D.toOMod m).obj L')) :=
  Stacks.SheafOfModules.RingSheafProductFactor.isZero_tensorObj_restrictScalars
    D.presentation hmn L L'

/-- **A module over a factor is a retract of its tensor product with that factor.**  For `L` an
`O_n`-module read as an `O`-module, `L` is a retract of `O_n ⊗_O L` in `Mod(O)`. -/
theorem nonempty_retract_tensor_toOMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.O
    Nonempty (Retract ((D.toOMod n).obj L)
      (MonoidalCategory.tensorObj
        ((D.toOMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
        ((D.toOMod n).obj L))) :=
  Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_tensorObj_restrictScalars
    D.presentation n L

/-! ### The diagonal terms at the level of sheaves -/

/-- **Reading `O_n`-modules as `O`-modules commutes with the tensor product**:

`(A as an O-module) ⊗_O (B as an O-module) ≅ (A ⊗_{O_n} B) as an O-module`. -/
def tensorObjIsoToOMod (D : ProductDecomposition X) (n : ℤ)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.O
    letI := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
    MonoidalCategory.tensorObj ((D.toOMod n).obj A) ((D.toOMod n).obj B) ≅
      (D.toOMod n).obj (MonoidalCategory.tensorObj A B) :=
  Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars₂ D.presentation n A B

/-- If two `O_n`-modules have the unit module of `O_n` as their tensor product, then their tensor
product over `O`, both read as `O`-modules, is `O_n` read as an `O`-module. -/
def tensorObjIsoToOModUnit (D : ProductDecomposition X) (n : ℤ)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (e : letI := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
      MonoidalCategory.tensorObj A B ≅
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.O
    MonoidalCategory.tensorObj ((D.toOMod n).obj A) ((D.toOMod n).obj B) ≅
      (D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :=
  Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoFactorModule D.presentation n A B e

/-! ### The orthogonality in the derived category -/

variable [HasDerivedCategory.{d} (Mod X.O)]

/-- **The derived orthogonality of the factors, one of the two modules being flat.**  For
`n ≠ m`, an `O_n`-module `L` which is flat over `O` and an arbitrary `O_m`-module `L'` have
vanishing derived tensor product in `D(O)`, each placed in degree zero. -/
theorem isZero_derivedTensor_toOMod (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((D.toOMod n).obj L)) :
    letI := derivedMonoidal X.O
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod m).obj L'))) :=
  isZero_derivedTensorSingle_of_isZero_tensorObj_left X.O _ _ hL
    (D.isZero_tensor_toOMod hmn L L')

/-- **The derived orthogonality of the factors, the other module being flat.**  For `n ≠ m`, an
arbitrary `O_n`-module `L` and an `O_m`-module `L'` which is flat over `O` have vanishing derived
tensor product in `D(O)`, each placed in degree zero. -/
theorem isZero_derivedTensor_toOMod_right (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))
    (hL' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((D.toOMod m).obj L')) :
    letI := derivedMonoidal X.O
    letI := derivedSymmetric X.O
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod m).obj L'))) :=
  isZero_derivedTensorSingle_of_isZero_tensorObj_right X.O _ _ hL'
    (D.isZero_tensor_toOMod hmn L L')

/-- **The derived orthogonality of an arbitrary module over one factor against another factor,
with no flatness hypothesis.**  For `n ≠ m` and `L` an arbitrary `O_n`-module, `L` and the factor
`O_m`, each read as an `O`-module and placed in degree zero, have vanishing derived tensor
product. -/
theorem isZero_derivedTensor_toOMod_factor_right (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := derivedMonoidal X.O
    letI := derivedSymmetric X.O
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj
        ((D.toOMod m).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))) :=
  D.isZero_derivedTensor_toOMod_right hmn L _ (D.isFlat_toOMod_unit m)

/-- **An `O_m`-module placed in degree zero is a retract of `O_m ⊗^𝐋` itself in `D(O)`.** -/
theorem nonempty_retract_derivedTensor_toOMod (D : ProductDecomposition X) (m : ℤ)
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := derivedMonoidal X.O
    Nonempty (Retract ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod m).obj L'))
      (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj
          ((D.toOMod m).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod m).obj L')))) := by
  let := derivedMonoidal X.O
  obtain ⟨ret⟩ := D.nonempty_retract_tensor_toOMod m L'
  exact ⟨(ret.map (DerivedCategory.singleFunctor (Mod X.O) 0)).trans
    (Retract.ofIso (derivedTensorSingleIso.{u, d} X.O
      ((D.toOMod m).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))))
      ((D.toOMod m).obj L') (D.isFlat_toOMod_unit m)).symm)⟩

/-- **The derived orthogonality of the factors for arbitrary modules over distinct factors, with
no hypothesis at all.**  For `n ≠ m`, an arbitrary `O_n`-module `L` and an arbitrary `O_m`-module
`L'`, each read as an `O`-module and placed in degree zero, have vanishing derived tensor product
in `D(O)`. -/
theorem isZero_derivedTensor_toOMod_of_ne (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))) :
    letI := derivedMonoidal X.O
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj L))
      ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod m).obj L'))) := by
  let := derivedMonoidal X.O
  let := derivedSymmetric X.O
  obtain ⟨ret⟩ := D.nonempty_retract_derivedTensor_toOMod.{u, d} m L'
  refine isZero_of_retract (ret.map (MonoidalCategory.tensorLeft
    ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj L)))) ?_
  exact (isZero_tensorObj_of_isZero_left.{u, d} X.O _
      (D.isZero_derivedTensor_toOMod_factor_right hmn L)).of_iso
    (MonoidalCategory.associator _ _ _).symm

end ProductDecomposition

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
