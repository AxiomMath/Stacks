module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# The structure sheaf is a unit on the left for a derived tensor product

Let `(C, O)` be a ringed site, with any universes, and `T` a derived tensor product on `D(O)` in
the sense of `Stacks.SheafOfModules.DerivedTensorProduct`. The structure sheaf in degree zero is a
unit for `T` on the left: `O[0] ⊗^L_O E ≅ E`. This is the mirror image of
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, which is the unit on the right.

Every object of `D(O)` is `Q K` for a complex `K`; the left factor `O[0]` is K-flat, so the left
K-flat comparison `comparisonLeft` computes `O[0] ⊗^L_O Q K` as `Q Tot(O[0] ⊗_O K)`; the Koszul
symmetry of the total tensor complex (`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`) turns
that into `Q Tot(K ⊗_O O[0])`, which is `Q K` by the ordinary unit law
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.unitLeftIso`: `O[0] ⊗^L_O E ≅ E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {Y : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The structure sheaf in degree zero is a unit on the left for the derived tensor product**:
`O[0] ⊗^L_O E ≅ E`, for every object `E` of `D(O)`. The left factor is K-flat, so the left K-flat
comparison computes the derived tensor product as the total tensor complex, which the Koszul
symmetry and the ordinary unit law identify with a representative of `E`. -/
def unitLeftIso (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : DerivedModules.{u, v, w, d} Y) :
    (T.tensor.obj ((DerivedCategory.singleFunctor (Modules.{u, v, w} Y) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj E ≅ E :=
  let U := (HomologicalComplex.single (Modules.{u, v, w} Y) (ComplexShape.up ℤ) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  ((T.tensor.obj (DerivedCategory.Q.obj U)).mapIso eK).symm ≪≫
    T.comparisonLeft U K (Stacks.SheafOfModules.isKFlat_single_unit Y.O) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O U K ≪≫
        Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K) ≪≫ eK

end Stacks.SheafOfModules.DerivedTensorProduct

end
