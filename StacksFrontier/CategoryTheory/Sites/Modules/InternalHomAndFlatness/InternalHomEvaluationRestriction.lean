module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Evaluation of the internal Hom sheaf commutes with restriction to a slice site

Let `(C, O)` be a ringed site, `U` an object of `C` and `F` a sheaf of `O`-modules. Restricting
to the localized site `C/U` is a right adjoint, and Stacks 0E8H
(`Stacks.SheafOfModules.ExtensionByZero.internalHomRestrictionNatIso`) says that it commutes
with the internal Hom sheaf out of `F`. That isomorphism compares the two *right* adjoints of
the tensor--internal-Hom correspondence of Stacks 03EO on `C` and on `C/U`, so it has a mate
comparing the two *left* adjoints,

`A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U`,

and the mate correspondence identifies the two counits. The counit of Stacks 03EO is the
evaluation morphism of the internal Hom sheaf, so that identification is exactly the statement
that evaluation commutes with restriction to a slice site.

## Main definitions

* `Stacks.SheafOfModules.ExtensionByZero.tensorRestrictionComparison`: the comparison
  `A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U`, defined as the mate of Stacks 0E8H under the
  correspondence of Stacks 03EO on `C` and on `C/U`.

## Main results

* `Stacks.SheafOfModules.ExtensionByZero.tensorRestrictionComparison_internalHomEvaluation`:
  **evaluation commutes with restriction to a slice site.** Restricting `Hom_O(F, A)` to `C/U`,
  reading it as `Hom_{O|_U}(F|_U, A|_U)` by Stacks 0E8H and evaluating there is the same as
  comparing the two tensor products and restricting the evaluation of `Hom_O(F, A)`.
* `Stacks.SheafOfModules.ExtensionByZero.tensorEvaluation_internalHomRestrictionNatIso`: the
  same identity written with `Stacks.SheafOfModules.InternalHom.tensorEvaluation`, which is the
  spelling in which `Stacks.SheafOfModules.InternalHom.tensorEvaluation_injective` consumes it.

## Implementation notes

Both the comparison and the identity are single applications of Mathlib's mate correspondence,
`CategoryTheory.mateEquiv` and `CategoryTheory.mateEquiv_counit_symm`, at the pair of
adjunctions `Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction` on `C` and on
`C/U`. That is the handedness in which the evaluation morphism is the counit: the left adjoint
there is `- ⊗_O F`, tensoring the *first* variable of
`Stacks.SheafOfModules.Tensor.sheafTensor`, so the comparison's domain is
`(sheafTensor (O|_U)).obj (A|_U) |>.obj (F|_U)` with `A|_U` in the first slot, which is the slot
`Stacks.SheafOfModules.InternalHom.tensorEvaluation` puts a morphism into the internal Hom sheaf
in.

No new mathematics about the tensor product is needed, and in particular none of the existing
isomorphisms identifying a tensor product with its restriction to a slice is used: the whole
content is that the comparison here is *the mate of Stacks 0E8H*, which is what makes it compose
with evaluation, and that property pins it down among them.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.InternalHom (internalHomSecondFunctor internalHomEvaluation
  tensorEvaluation sheafTensorRightHomAdjunction)

namespace Stacks.SheafOfModules.ExtensionByZero

universe u

section EvaluationRestriction

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The comparison `A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U`**, as the mate of Stacks 0E8H.

Restriction to `C/U` is the vertical functor on both sides of the square of adjunctions formed
by the tensor--internal-Hom correspondence of Stacks 03EO on `C` and on `C/U`; Stacks 0E8H is a
2-cell between the two right adjoints, and this is the 2-cell between the two left adjoints that
the mate correspondence attaches to it. Defining it this way, rather than building it from the
tensor product directly, is what makes
`tensorRestrictionComparison_internalHomEvaluation` available. -/
def tensorRestrictionComparison :
    TwoSquare (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      ((sheafTensor X.O).flip.obj F)
      ((sheafTensor (X.O.over U)).flip.obj (F.over U))
      (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  (mateEquiv (sheafTensorRightHomAdjunction X.O F)
      (sheafTensorRightHomAdjunction (X.O.over U) (F.over U))).symm
    (TwoSquare.mk _ _ _ _ (internalHomRestrictionNatIso X U F).hom)

/-- **Evaluation of the internal Hom sheaf commutes with restriction to a slice site.**
Restricting `Hom_O(F, A)` to `C/U`, reading the result as `Hom_{O|_U}(F|_U, A|_U)` by
Stacks 0E8H, tensoring with `F|_U` and evaluating there is the same as comparing the two tensor
products by `tensorRestrictionComparison` and restricting the evaluation morphism of
`Hom_O(F, A)`.

This is `CategoryTheory.mateEquiv_counit_symm` at the two correspondences of Stacks 03EO, whose
counit is the evaluation morphism. -/
theorem tensorRestrictionComparison_internalHomEvaluation
    (A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((sheafTensor (X.O.over U)).flip.obj (F.over U)).map
          ((internalHomRestrictionNatIso X U F).hom.app A) ≫
        internalHomEvaluation (X.O.over U) (F.over U) (A.over U) =
      (tensorRestrictionComparison X U F).natTrans.app
          ((internalHomSecondFunctor X.J X.O F).obj A) ≫
        (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (internalHomEvaluation X.O F A) :=
  mateEquiv_counit_symm (sheafTensorRightHomAdjunction.{u, u} X.O F)
    (sheafTensorRightHomAdjunction.{u, u} (X.O.over U) (F.over U))
    (TwoSquare.mk _ _ _ _ (internalHomRestrictionNatIso X U F).hom) A

/-- **Evaluation commutes with restriction to a slice site**, written with
`Stacks.SheafOfModules.InternalHom.tensorEvaluation`.

This is `tensorRestrictionComparison_internalHomEvaluation` with its left-hand side folded into
the tensor--evaluate composite that
`Stacks.SheafOfModules.InternalHom.tensorEvaluation_injective` is stated against, so that an
identity between two morphisms into a restricted internal Hom sheaf can be reduced to one
between morphisms out of a tensor product on the slice site. -/
theorem tensorEvaluation_internalHomRestrictionNatIso
    (A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tensorEvaluation (X.O.over U) (F.over U) (A.over U)
        ((internalHomRestrictionNatIso X U F).hom.app A) =
      (tensorRestrictionComparison X U F).natTrans.app
          ((internalHomSecondFunctor X.J X.O F).obj A) ≫
        (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (internalHomEvaluation X.O F A) :=
  tensorRestrictionComparison_internalHomEvaluation X U F A

end EvaluationRestriction

end Stacks.SheafOfModules.ExtensionByZero

end
