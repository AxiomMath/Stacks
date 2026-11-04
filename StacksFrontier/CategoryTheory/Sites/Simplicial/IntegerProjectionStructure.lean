module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLiftZero
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarStructure

/-!
# The comparison map of Stacks 0D9E against the structure maps of the integral resolution

Let `S` be a simplicial-site situation. All names are in the namespace
`CategoryTheory.SimplicialSiteSituation`. The comparison `integerProjectionSheaf` of
Stacks 0D9E (1) is the map `g_{n!}(F_n) ⟶ g_{n!}ℤ ⊗_ℤ F` of abelian sheaves on the total site, the
comparison `componentLowerShriekMap'` with the degree-`n` term of the simplex-coefficient
resolution of Stacks 0D78 followed by the projection formula `barTermIsoIntegerTensor`. This file
computes the comparison against the augmentation and the structure maps of the integral resolution
of Stacks 09WI.

## Main results

* `integerProjectionSheaf_comp_integerTensorAugmentation`: **the comparison of degree zero followed
  by the augmentation `g_{0!}ℤ ⊗_ℤ F ⟶ F` is the counit of `g_{0!} ⊣ g_0^{-1}`.**
* `integerProjectionSheaf_app_comp_integerTensorFace_app`: **the comparison of degree `q` followed
  by the structure map of `φ : ⦋p⦌ ⟶ ⦋q⦌` is the transpose along `g_{q!} ⊣ g_q^{-1}` of the
  `φ`-labelled summand of the degree-`p` term, read through the projection formula.**
* `fiberTransition_comp_integerProjectionSheaf_comp_integerTensorFace`: the same with the summand
  replaced by the `φ`-labelled leg of the direct-sum formula of Stacks 09WG and the comparison of
  degree `p`, both sides transported along the inverse-image transition of Stacks 07TF.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- **The comparison of Stacks 0D9E in degree zero, followed by the augmentation of the integral
resolution, is the counit of `g_{0!} ⊣ g_0^{-1}`**, at an abelian sheaf. -/
theorem integerProjectionSheaf_app_comp_integerTensorAugmentation_app
    (F : Sheaf S.totalTopology Ab.{u}) :
    (integerProjectionSheaf S ⦋0⦌).app F ≫ (integerTensorAugmentation S).app F =
      (S.componentLowerShriekAbAdjunction' ⦋0⦌).counit.app F := by
  rw [integerProjectionSheaf, NatTrans.comp_app, Category.assoc,
    ← barTermIsoIntegerTensor_augmentation S F]
  exact componentLowerShriekMap_comp_barAugmentation S F

/-- **The comparison of Stacks 0D9E in degree zero, followed by the augmentation of the integral
resolution, is the counit of `g_{0!} ⊣ g_0^{-1}`**, as natural transformations. -/
theorem integerProjectionSheaf_comp_integerTensorAugmentation :
    integerProjectionSheaf S ⦋0⦌ ≫ integerTensorAugmentation S =
      (S.componentLowerShriekAbAdjunction' ⦋0⦌).counit :=
  NatTrans.ext (funext fun F =>
    integerProjectionSheaf_app_comp_integerTensorAugmentation_app S F)

/-- **The comparison of Stacks 0D9E in degree `q`, followed by the structure map of the integral
resolution at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the transpose along `g_{q!} ⊣ g_q^{-1}` of the `φ`-labelled
summand of the degree-`p` term of the simplex-coefficient resolution, read through the projection
formula.** -/
theorem integerProjectionSheaf_app_comp_integerTensorFace_app
    {p q : SimplexCategory} (φ : p ⟶ q) (F : Sheaf S.totalTopology Ab.{u}) :
    (integerProjectionSheaf S q).app F ≫ (integerTensorFace S φ).app F =
      ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
          (S.componentSheafSummand' F φ) ≫
        (barTermIsoIntegerTensor S p).hom.app F := by
  rw [integerProjectionSheaf, NatTrans.comp_app, Category.assoc,
    ← barTermIsoIntegerTensor_face S φ F, ← Category.assoc,
    componentLowerShriekMap_comp_barSimplicial_map']

section Summand

attribute [local instance] componentFunctorHasCoproductsOfShape
attribute [local instance] hasColimitsOfShapeDiscreteSheafComponent

/-- **The comparison of Stacks 0D9E against the structure map of the integral resolution, read
through the direct-sum formula of Stacks 09WG.** The comparison of degree `q` followed by the
structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌`, both transported along the inverse-image transition of
Stacks 07TF at `φ`, is the transpose along `g_{q!} ⊣ g_q^{-1}` of the `φ`-labelled leg of the
direct-sum formula, followed by the comparison of degree `p`. -/
theorem fiberTransition_comp_integerProjectionSheaf_comp_integerTensorFace
    {p q : SimplexCategory} (φ : p ⟶ q) (F : Sheaf S.totalTopology Ab.{u}) :
    (componentLowerShriekAb S q).map ((S.fiberTransitionAb' φ).app F) ≫
        (integerProjectionSheaf S q).app F ≫ (integerTensorFace S φ).app F =
      ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
          ((S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F)) ≫
        (integerProjectionSheaf S p).app F := by
  calc (componentLowerShriekAb S q).map ((S.fiberTransitionAb' φ).app F) ≫
          (integerProjectionSheaf S q).app F ≫ (integerTensorFace S φ).app F
      = (componentLowerShriekAb S q).map ((S.fiberTransitionAb' φ).app F) ≫
          ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
              (S.componentSheafSummand' F φ) ≫
            (barTermIsoIntegerTensor S p).hom.app F := by
        rw [integerProjectionSheaf_app_comp_integerTensorFace_app]
    _ = ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
            ((S.fiberTransitionAb' φ).app F ≫ S.componentSheafSummand' F φ) ≫
          (barTermIsoIntegerTensor S p).hom.app F := by
        rw [← Category.assoc,
          (S.componentLowerShriekAbAdjunction' q).homEquiv_naturality_left_symm]
    _ = ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
            ((S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F) ≫
              (S.restrictAb q).map ((componentLowerShriekMap' S p).app F)) ≫
          (barTermIsoIntegerTensor S p).hom.app F := by
        rw [componentSumFormulaLeg_comp_restrictAb_map_componentLowerShriekMap]
        rfl
    _ = ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
            ((S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F)) ≫
          (componentLowerShriekMap' S p).app F ≫
            (barTermIsoIntegerTensor S p).hom.app F := by
        rw [(S.componentLowerShriekAbAdjunction' q).homEquiv_naturality_right_symm,
          Category.assoc]
    _ = ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
            ((S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F)) ≫
          (integerProjectionSheaf S p).app F := by
        rw [integerProjectionSheaf, NatTrans.comp_app]

end Summand

end CategoryTheory.SimplicialSiteSituation

end
