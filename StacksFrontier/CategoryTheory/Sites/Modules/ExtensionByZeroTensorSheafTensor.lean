module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorBifunctorial
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# Extension by zero and the tensor product, in the spelling of the tensor bifunctor

`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso` and its naturality
`restrictionTensorIso_naturality_right` in the sheaf of modules on the big site are stated
through `(Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip`, tensoring on the right with a
fixed sheaf of modules: the morphism of tensor functors induced by `α : F ⟶ F'` is `flip.map α`
there.  The total complex of a pair of complexes and
`Stacks.SheafOfModules.DerivedTensorProduct` are instead stated through the action of the
bifunctor on its second variable, `((sheafTensor X.O).obj A).map α`.

This file records that the passage between the two costs nothing: the component of `flip.map α`
at `A` *is* that action, and that action *is* the sheafification of the objectwise morphism,
both by definition.  The naturality of Stacks 0E8I in the module on the big site is therefore
available directly in the bifunctor's own spelling.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.sheafTensor_obj_map`: the identification of
  the action of the bifunctor on its second variable with the sheafification of the objectwise
  morphism, by definition.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionSheafTensor_naturality_right`:
  **Stacks 0E8I is natural in the module on the big site**, with the morphism of tensor functors
  read as the action of `Stacks.SheafOfModules.Tensor.sheafTensor` on `α`.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

open Stacks.Sites.OverModules
open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (sheafTensor)

section BigSite

variable (X : RingedSite.{c, u, u})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The tensor bifunctor acts on a morphism of its second variable by sheafifying the
objectwise morphism**, that morphism being the extension formula's
`FormulaExtension.tensorRightMap`, in which the steps of `restrictionTensorIso` are given. -/
lemma sheafTensor_obj_map (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {F F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : F ⟶ F') :
    ((sheafTensor.{c, u, u} X.O).obj A).map α =
      (sheafifyModules X.J X.O).map (FormulaExtension.tensorRightMap X.O.obj A.val α.val) :=
  rfl

end BigSite

section Slice

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 0E8I is natural in the sheaf of modules on `X`**, with the vertical morphisms read
as the action of the tensor bifunctor on `α` rather than as the component of
`(sheafTensor X.O).flip.map α`, the spelling `restrictionTensorIso_naturality_right` is given
in.  The two readings agree by the definition of `CategoryTheory.Functor.flip`. -/
lemma restrictionSheafTensor_naturality_right
    {F F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : F ⟶ F')
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    ((sheafTensor.{c, u, u} X.O).obj ((extendByZero X U).obj G)).map α ≫
        (restrictionTensorIso X U F').hom.app G =
      (restrictionTensorIso X U F).hom.app G ≫
        (extendByZero X U).map (sliceTensorRightMap X U α G) :=
  restrictionTensorIso_naturality_right X U α G

end Slice

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

end
