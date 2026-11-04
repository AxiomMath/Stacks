module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle

/-!
# The map `(f_*M)[0] ⟶ Rf_*(M[0])` in the spelling of the small étale ringed topoi

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `φ` the morphism of small étale ringed
topoi of `f`. The total right derived direct image `Rφ_*` of the ringed topoi comes with its unit
`φ_* ⟶ Rφ_*` on homotopy categories. Read at complexes in degree `0`, the unit is the canonical
map `(φ_*M)[0] ⟶ Rφ_*(M[0])`, `Stacks.DerivedFunctor.singleUnit`. This file records that map
for the modules of the ringed topos `AlgebraicGeometry.Space.smallEtaleRingedTopos X`, the
spelling in which the generic derived direct image of ringed topoi is stated. It compares the
map with the canonical map `AlgebraicGeometry.Space.modulePushforwardSingleToDerived` of the
site spelling, and deduces that the map is invertible for an affine `f` and a quasi-coherent `M`
(Stacks 073H).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleUnit`: the map
  `(φ_*M)[0] ⟶ Rφ_*(M[0])`, natural in `M`.
* `AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleIsoOfIsAffineHom`: its inverse
  `Rφ_*(M[0]) ≅ (φ_*M)[0]` for an affine `f` and a quasi-coherent `M`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `modulePushforwardSingleToDerived_eq_comp_smallEtaleToposPushforwardSingleUnit`,
  `smallEtaleToposPushforwardSingleUnit_eq_comp_modulePushforwardSingleToDerived`: the comparison
  with the site spelling, as natural transformations.
* `isIso_smallEtaleToposPushforwardSingleUnit_app_of_isAffineHom`: the map is invertible at a
  quasi-coherent module along an affine morphism.

## Implementation notes

The modules of the small étale ringed site and those of the small étale ringed topos are the
same category in two spellings. The two direct images of modules are equal, but not
definitionally (`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`). The
comparison is therefore stated between natural transformations. A component is obtained
from it by `NatTrans.congr_app`, at an object shared by both sides. Comparing components of
differently spelled terms directly is much more expensive for the kernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The canonical map `(f_*M)[0] ⟶ RF(M[0])` of a right derived functor `RF` of the direct image
of modules, with unit `α`, is `Stacks.DerivedFunctor.singleUnit` of the direct image. -/
theorem modulePushforwardSingleToRightDerived_eq_singleUnit (f : X ⟶ Y)
    (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF) :
    modulePushforwardSingleToRightDerived B S hS f RF α =
      Stacks.DerivedFunctor.singleUnit (modulePushforward B S hS f) RF α := by
  ext M
  simp [modulePushforwardSingleToRightDerived, Stacks.DerivedFunctor.singleUnit]

/-- **The canonical map `(φ_*M)[0] ⟶ Rφ_*(M[0])`** for the morphism `φ` of small étale ringed
topoi of `f`: the unit of the total right derived direct image `Rφ_*`, read at the complexes in
degree `0` (`Stacks.DerivedFunctor.singleUnit`). -/
def smallEtaleToposPushforwardSingleUnit (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙ DerivedCategory.singleFunctor _ 0 ⟶
      DerivedCategory.singleFunctor _ 0 ⋙
        derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) :=
  Stacks.DerivedFunctor.singleUnit _ _
    ((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O)) (ComplexShape.up ℤ)))

/-- **The canonical map of the site spelling through that of the ringed topoi**:
`AlgebraicGeometry.Space.modulePushforwardSingleToDerived` is the identification
`f_* ⋙ [0] ≅ φ_* ⋙ [0]` followed by
`AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleUnit`. -/
theorem modulePushforwardSingleToDerived_eq_comp_smallEtaleToposPushforwardSingleUnit
    (f : X ⟶ Y) :
    modulePushforwardSingleToDerived B S hS f =
      (Functor.isoWhiskerRight (eqToIso (pushforwardModules_eq_modulePushforward B S hS f))
          (DerivedCategory.singleFunctor _ 0)).inv ≫
        smallEtaleToposPushforwardSingleUnit B S hS f :=
  (modulePushforwardSingleToRightDerived_eq_singleUnit B S hS f _ _).trans
    (Stacks.DerivedFunctor.singleUnit_eqToHom_comp (modulePushforward B S hS f)
      (smallEtaleRingedToposHom B S hS f).pushforwardModules
      (hw₂ := additive_smallEtaleRingedToposHom_pushforwardModules B S hS f)
      (pushforwardModules_eq_modulePushforward B S hS f) _ _ _)

/-- `AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleUnit` is the identification
`φ_* ⋙ [0] ≅ f_* ⋙ [0]` followed by the canonical map
`AlgebraicGeometry.Space.modulePushforwardSingleToDerived` of the site spelling. -/
theorem smallEtaleToposPushforwardSingleUnit_eq_comp_modulePushforwardSingleToDerived
    (f : X ⟶ Y) :
    smallEtaleToposPushforwardSingleUnit B S hS f =
      (Functor.isoWhiskerRight (eqToIso (pushforwardModules_eq_modulePushforward B S hS f))
          (DerivedCategory.singleFunctor _ 0)).hom ≫ modulePushforwardSingleToDerived B S hS f :=
  (Stacks.DerivedFunctor.singleUnit_eq_comp_eqToHom (modulePushforward B S hS f)
      (smallEtaleRingedToposHom B S hS f).pushforwardModules
      (hw₂ := additive_smallEtaleRingedToposHom_pushforwardModules B S hS f)
      (pushforwardModules_eq_modulePushforward B S hS f) _ _ _).trans
    (congrArg (_ ≫ ·) (modulePushforwardSingleToRightDerived_eq_singleUnit B S hS f _ _).symm)

/-- **`(φ_*M)[0] ⟶ Rφ_*(M[0])` is invertible for an affine morphism `f` and a quasi-coherent
module `M`** (Stacks 073H), by comparison with the site spelling
(`AlgebraicGeometry.Space.isIso_modulePushforwardSingleToDerived_app_of_isAffineHom`). -/
theorem isIso_smallEtaleToposPushforwardSingleUnit_app_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((smallEtaleToposPushforwardSingleUnit B S hS f).app M) := by
  have := isIso_modulePushforwardSingleToDerived_app_of_isAffineHom B S hS f hf M hM
  have e := (NatTrans.congr_app
    (smallEtaleToposPushforwardSingleUnit_eq_comp_modulePushforwardSingleToDerived B S hS f)
      M).trans (NatTrans.comp_app _ _ M)
  rw [e]
  exact IsIso.comp_isIso' (Iso.isIso_hom (Iso.app (Functor.isoWhiskerRight
    (eqToIso (pushforwardModules_eq_modulePushforward B S hS f))
      (DerivedCategory.singleFunctor _ 0)) M)) this

/-- **`Rφ_*(M[0]) ≅ (φ_*M)[0]` for an affine morphism `f` and a quasi-coherent module `M`**:
the inverse of the canonical map
`AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleUnit`. -/
def smallEtaleToposPushforwardSingleIsoOfIsAffineHom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
    (hM : M.IsQuasicoherentOnSite) :
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj M) :=
  (@asIso _ _ _ _ ((smallEtaleToposPushforwardSingleUnit B S hS f).app M)
    (isIso_smallEtaleToposPushforwardSingleUnit_app_of_isAffineHom B S hS f hf M hM)).symm

/-- The inverse of `AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleIsoOfIsAffineHom` is
the canonical map. -/
theorem smallEtaleToposPushforwardSingleIsoOfIsAffineHom_inv (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
    (hM : M.IsQuasicoherentOnSite) :
    (smallEtaleToposPushforwardSingleIsoOfIsAffineHom B S hS f hf M hM).inv =
      (smallEtaleToposPushforwardSingleUnit B S hS f).app M :=
  rfl

end AlgebraicGeometry.Space
