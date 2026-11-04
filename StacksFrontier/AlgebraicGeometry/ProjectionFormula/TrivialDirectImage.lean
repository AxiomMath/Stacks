module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Monoidal
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SourceDimension

/-!
# Pulling back an invertible module along a morphism with `Rc_* 𝒪_X = 𝒪_Y`

Let `c : X ⟶ Y` be a morphism of schemes and `𝒩` an invertible `𝒪_Y`-module. By the projection
formula ([Stacks, Tag 01E8]) `R^n c_*(c^* 𝒩) = R^n c_* 𝒪_X ⊗ 𝒩`, so a vanishing `R^n c_* 𝒪_X`
gives a vanishing `R^n c_*(c^* 𝒩)`, and `𝒪_Y = c_* 𝒪_X` gives `c_* c^* 𝒩 = 𝒩`.

## Main results

* `Stacks.ProjectionFormula.isZero_rightDerived_pullback_of_isZero_rightDerived_unit`:
  `R^n c_*(c^* 𝒩) = 0` when `R^n c_* 𝒪_X = 0`.
* `Stacks.ProjectionFormula.pushforwardPullbackIsoOfIsIso`: `c_* c^* 𝒩 ≅ 𝒩` when
  `𝒪_Y ⟶ c_* 𝒪_X` is an isomorphism.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (c : X ⟶ Y) (N : Y.Modules)
  [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]

/-- **`R^n c_*(c^* 𝒩) = 0` when `R^n c_* 𝒪_X = 0`**, for an invertible `𝒩`. -/
theorem isZero_rightDerived_pullback_of_isZero_rightDerived_unit (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      ((Scheme.Modules.pullback c).obj N)) := by
  have h' : IsZero (((Scheme.Modules.pushforward c).rightDerivedPlus (n : ℤ)).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
    h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward c) n).app
      _).symm
  refine (((tensorRightInvertible Y N).map_isZero h').of_iso ?_).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward c) n).app _)
  exact ((Scheme.Modules.pushforward c).rightDerivedPlus (n : ℤ)).mapIso
      (AlgebraicGeometry.tensorSheafUnitLeft X.toRingedSpace _).symm ≪≫
    higherDirectImageProjectionFormulaIso c N (SheafOfModules.unit X.ringCatSheaf) n

/-- **`c_* c^* 𝒩 ≅ 𝒩` when `𝒪_Y = c_* 𝒪_X`**, for an invertible `𝒩`: the projection formula
`c_*(𝒪_X ⊗ c^* 𝒩) = c_* 𝒪_X ⊗ 𝒩` followed by the inverse of `𝒪_Y ⟶ c_* 𝒪_X`. -/
def pushforwardPullbackIsoOfIsIso
    (h : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pullback c).obj N) ≅ N :=
  (Scheme.Modules.pushforward c).mapIso
      (AlgebraicGeometry.tensorSheafUnitLeft X.toRingedSpace _).symm ≪≫
    (pushforwardTensorRightNatIso c N).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (tensorRightInvertible Y N).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)).symm ≪≫
    AlgebraicGeometry.tensorSheafUnitLeft Y.toRingedSpace N

end Stacks.ProjectionFormula
