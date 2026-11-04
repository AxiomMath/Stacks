module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalUnitality

/-!
# The collapse of a total tensor complex at a trivialised single-degree second factor

Let `X` be a ringed site, let `Y` be a complex of `O`-modules and let `Z` be a complex vanishing
outside a single degree `k` with `Z^k ≅ O`. In each total degree `n` the total tensor complex
`Tot(Y ⊗_O Z)` is then just `Y^{-k+n}`, and the identification sends a section `y` to the local
pure tensor of `y` with the section of `Z^k` corresponding to `1`.

The degreewise isomorphism is the composite of
`AlgebraicGeometry.RingedSite.unitFactorRightIso` with the inclusion of the surviving summand,
an isomorphism by `AlgebraicGeometry.RingedSite.isIso_ιTotal_of_unitFactorRight`, and the
comparison `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`; this file describes it on
local sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitRightFactorIso`: the collapse `Y^{-k+n} ≅ Tot(Y ⊗_O Z)^n`.
* `AlgebraicGeometry.RingedSite.unitRightFactorIsoAt`: the same with the degree of `Y` supplied as
  a variable `m` together with `m + k = c` rather than computed as `-k + c`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafTensor_obj_map_app_sheafifyUnit_tmul`: tensoring a local pure
  tensor by a morphism in the **right-hand** factor; the left-hand companion is
  `Stacks.SheafOfModules.ExtensionByZero.sheafTensor_map_app_sheafifyUnit_tmul`.
* `AlgebraicGeometry.RingedSite.unitRightFactorIsoAt_hom_apply`: the collapse on local sections.

## References

* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Lemma 20.49.6 (Tag 0A92)](https://stacks.math.columbia.edu/tag/0A92)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tensoring a local pure tensor by `ψ` in the right-hand factor.** The image of `y ⊗ x` under
`M ⊗ ψ` is `y ⊗ ψ x`. -/
theorem sheafTensor_obj_map_app_sheafifyUnit_tmul
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (ψ : G ⟶ G')
    (U : X.Cᵒᵖ) (y : M.val.obj U) (x : G.val.obj U) :
    (((sheafTensor.{u, u, u, u, u} X.O).obj M).map ψ).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X.O.obj) M.val G.val)).app U
          (y ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.O.obj) M.val G'.val)).app U
        (y ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] ψ.val.app U x) :=
  (congrArg (fun z => z.app U (y ⊗ₜ[(ringSheaf X.O).obj.obj U] x))
    ((PresheafOfModules.sheafificationAdjunction (R := ringSheaf X.O)
      (𝟙 (ringSheaf X.O).obj)).unit.naturality
        (PresheafOfModules.tensorHom (O := X.O.obj) (𝟙 M.val) ψ.val))).symm

variable [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

variable {Y Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (k : ℤ) (e : Z.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (hZ : ∀ q, q ≠ k → IsZero (Z.X q))

/-- **The collapse of the total tensor complex at a trivialised single-degree second factor**, in
total degree `n`: the trivialisation of the surviving factor, the inclusion of the surviving
summand, and the comparison of the two models of the total tensor complex. -/
def unitRightFactorIso (n : ℤ) : Y.X (-k + n) ≅ (tensorTotal X Y Z).X n :=
  unitFactorRightIso X k e n ≪≫
    (@asIso _ _ _ _ _ (isIso_ιTotal_of_unitFactorRight X k n hZ)) ≪≫
      (HomologicalComplex.eval (SheafOfModules.{u} (ringSheaf X.O)) (ComplexShape.up ℤ) n).mapIso
        (tensorTotalIsoTensorComplex X Y Z).symm

/-- **The collapse carries a section to the local pure tensor with the trivialising section.** -/
lemma unitRightFactorIso_hom_apply (n : ℤ) (W : X.C) (y : (Y.X (-k + n)).val.obj (op W)) :
    (unitRightFactorIso X k e hZ n).hom.val.app (op W) y =
      tensorTotalSectionAt X Y Z W (-k + n) k n (by omega) y
        (e.inv.val.app (op W)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) := by
  have h0 : (unitRightFactorIso X k e hZ n).hom.val.app (op W) y =
      ((tensorTotalIsoTensorComplex X Y Z).inv.f n).val.app (op W)
        ((HomologicalComplex.ιMapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ) (-k + n) k n (by simp)).val.app (op W)
          ((((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + n))).map e.inv).val.app (op W)
            ((sheafTensorUnitIsoRight.{u, u, u} X.O (Y.X (-k + n))).inv.val.app (op W) y))) :=
    rfl
  rw [h0, sheafTensorUnitIsoRight_inv_apply]
  erw [sheafTensor_obj_map_app_sheafifyUnit_tmul]
  exact tensorTotalIsoTensorComplex_inv_tensorComplexSection X Y Z W (-k + n) k n (by omega) y
    (e.inv.val.app (op W) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)))

/-- **The collapse with the degree of `Y` given as an independent variable** `m`, together with
`m + k = c`, rather than computed as `-k + c`. -/
def unitRightFactorIsoAt (m c : ℤ) (h : m + k = c) : Y.X m ≅ (tensorTotal X Y Z).X c :=
  (Y.XIsoOfEq (by omega : m = -k + c)) ≪≫ unitRightFactorIso X k e hZ c

/-- **The free-degree collapse sends a section to the local pure tensor with the trivialising
section.** -/
lemma unitRightFactorIsoAt_hom_apply (m c : ℤ) (h : m + k = c) (W : X.C)
    (y : (Y.X m).val.obj (op W)) :
    (unitRightFactorIsoAt X k e hZ m c h).hom.val.app (op W) y =
      tensorTotalSectionAt X Y Z W m k c h y
        (e.inv.val.app (op W)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) := by
  obtain rfl : m = -k + c := by omega
  exact unitRightFactorIso_hom_apply X k e hZ c W y

end AlgebraicGeometry.RingedSite

end
