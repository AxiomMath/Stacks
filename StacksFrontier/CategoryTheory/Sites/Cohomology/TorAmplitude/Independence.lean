module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs

/-!
# Tor amplitude does not depend on the choice of derived tensor product

Let `X` be a ringed site whose morphisms, structure sheaf and modules lie in one universe (the
objects being free), so that every complex of `𝒪_X`-modules has a K-flat resolution
(Stacks 06YS). Any two derived tensor products `T`, `T'` on `D(𝒪_X)`, in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`, then agree on objects: both compute `E ⊗^L L` from
a K-flat representative of `E` as the total tensor complex. In particular Tor amplitude
(Stacks 08FZ) read against `T` and against `T'` are the same condition.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.tensorObjIso`: `E ⊗_T L ≅ E ⊗_{T'} L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe c u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{c, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Two derived tensor products agree on objects**: through a K-flat representative `P` of
`E`, both `E ⊗_T L` and `E ⊗_{T'} L` are the image of the total tensor complex of `P` with a
representative of `L`. -/
def tensorObjIso (T T' : DerivedTensorProduct.{c, u, u, d} X)
    (E L : RingedSite.DerivedModules.{c, u, u, d} X) :
    (T.tensor.obj E).obj L ≅ (T'.tensor.obj E).obj L :=
  let K := DerivedCategory.Q.objPreimage E
  let h := Stacks.SheafOfModules.exists_kFlat_quasiIso X K
  let P := h.choose
  let p := h.choose_spec.choose
  have hP : Stacks.SheafOfModules.IsKFlat X.O P := h.choose_spec.choose_spec.1
  have : QuasiIso p := h.choose_spec.choose_spec.2
  let eE : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let L' := DerivedCategory.Q.objPreimage L
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  (T.tensor.mapIso eE.symm).app L ≪≫ (T.tensor.obj (DerivedCategory.Q.obj P)).mapIso eL.symm ≪≫
    T.comparisonLeft P L' hP ≪≫ (T'.comparisonLeft P L' hP).symm ≪≫
    (T'.tensor.obj (DerivedCategory.Q.obj P)).mapIso eL ≪≫ (T'.tensor.mapIso eE).app L

end Stacks.SheafOfModules.DerivedTensorProduct

end
