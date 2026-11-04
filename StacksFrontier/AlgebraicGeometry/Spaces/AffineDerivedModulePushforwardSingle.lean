module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection

/-!
# The derived direct image of a quasi-coherent module along an affine morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, with derived direct image `Rf_* = AlgebraicGeometry.Space.derivedModulePushforward f`.  The
unit of `Rf_*` as a right derived functor of the direct image of modules, read at the complexes
`M[0]`, is a canonical map `(f_*M)[0] ⟶ Rf_*(M[0])`.  If `f` is affine and `M` is quasi-coherent
this map is an isomorphism: `Rf_*(M[0])` lives in degree `0` (it lives in degrees `≥ 0` for every
`f`, and in degrees `≤ 0` by Stacks 073H through
`AlgebraicGeometry.Space.isLE_rightDerived_modulePushforward_of_isAffineHom`), and in degree `0`
the map is `f_* ⟶ R⁰f_*`, invertible because `f_*` is left exact.  In particular
`f_*𝒪_X ⟶ Rf_*𝒪_X` is an isomorphism for affine `f`, the first step of the proof of
Stacks 08IJ.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardSingleToDerived`: the canonical map
  `(f_*M)[0] ⟶ Rf_*(M[0])`, natural in `M`.
* `AlgebraicGeometry.Space.derivedModulePushforwardSingleHomologyZeroIso`:
  `H⁰(Rf_*(M[0])) ≅ f_*M`, natural in `M`, for every `f`.
* `AlgebraicGeometry.Space.derivedModulePushforwardSingleIsoOfIsAffineHom`:
  `Rf_*(M[0]) ≅ (f_*M)[0]` for affine `f` and quasi-coherent `M`.
* `AlgebraicGeometry.Space.derivedModulePushforwardStructureModuleIso`:
  `Rf_*𝒪_X ≅ f_*𝒪_X` for affine `f`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 08IJ](https://stacks.math.columbia.edu/tag/08IJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

section RightDerived

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (f : X ⟶ Y)
  (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)

/-- **The canonical map `(f_*M)[0] ⟶ RF(M[0])`** of a right derived functor `RF` of the direct
image with unit `α`: the unit at the complexes `M[0]`. -/
def modulePushforwardSingleToRightDerived :
    modulePushforward B S hS f ⋙ DerivedCategory.singleFunctor _ 0 ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ RF :=
  (Stacks.DerivedFunctor.mapSingleQhIso (modulePushforward B S hS f) 0).inv ≫
    Functor.whiskerLeft (HomotopyCategory.singleFunctor _ 0) α ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQh _ 0).inv RF

variable [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

include α in
/-- A right derived functor of the direct image carries `D^{≥ n}` into `D^{≥ n}`. -/
theorem isGE_rightDerived_modulePushforward_obj
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ) (hE : E.IsGE n) :
    (RF.obj E).IsGE n :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS f) RF α
    (fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh RF α I hI)
    E n hE

include α in
/-- A right derived functor of the direct image carries a module placed in degree `0` into
degrees `≥ 0`. -/
theorem isGE_rightDerived_modulePushforward_obj_singleFunctor
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (RF.obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 0 :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS f) RF α
    (fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh RF α I hI)
    _ 0 inferInstance

include α in
/-- A right derived functor of the direct image along an affine morphism carries a
quasi-coherent module placed in degree `0` into degrees `≤ 0` (Stacks 073H). -/
theorem isLE_rightDerived_modulePushforward_obj_singleFunctor_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    (RF.obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE 0 := by
  refine isLE_rightDerived_modulePushforward_of_isAffineHom B S hS f RF α hf _
    (fun q => ?_) 0 inferInstance
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  by_cases hq : q = 0
  · subst hq
    exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · rcases lt_or_gt_of_ne hq with hq | hq
    · exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ 0 q hq)
    · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ 0 q hq)

/-- **The canonical map `(f_*M)[0] ⟶ RF(M[0])` is invertible for an affine morphism `f` and a
quasi-coherent module `M`.**  The target lives in degree `0`, and in degree `0` the map is
`f_* ⟶ R⁰f_*`, invertible because `f_*` is left exact. -/
theorem isIso_modulePushforwardSingleToRightDerived_app_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((modulePushforwardSingleToRightDerived B S hS f RF α).app M) := by
  have : PreservesFiniteLimits (modulePushforward B S hS f) :=
    have := (modulePullbackAdjunction B S hS f).rightAdjoint_preservesLimits
    inferInstance
  have := isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f RF α M
  have := isLE_rightDerived_modulePushforward_obj_singleFunctor_of_isAffineHom B S hS f RF α hf
    M hM
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS f) RF α
  rw [DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    have := Stacks.DerivedFunctor.isIso_singleUnitHomology_app (modulePushforward B S hS f) RF α
      (fun M => isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f RF α M)
      (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective _ _ _
        (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) J hJ) M
    rw [Stacks.DerivedFunctor.singleUnitHomology_app] at this
    simp only [modulePushforwardSingleToRightDerived, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp]
    infer_instance
  · rcases lt_or_gt_of_ne hn with hn | hn <;>
      refine isIso_of_source_target_iso_zero _ (?_ : IsZero _).isoZero (?_ : IsZero _).isoZero <;>
      dsimp only [Functor.comp_obj] <;>
      first
        | exact DerivedCategory.isZero_of_isGE _ 0 n hn
        | exact DerivedCategory.isZero_of_isLE _ 0 n hn

/-- **`H⁰(RF(M[0])) ≅ f_*M`, naturally in `M`,** for a right derived functor `RF` of the direct
image along any morphism `f`: the direct image is left exact, so the degree-`0` cohomology of the
unit at the complexes `M[0]` is invertible. -/
def rightDerivedModulePushforwardSingleHomologyZeroIso :
    DerivedCategory.singleFunctor _ 0 ⋙ RF ⋙ DerivedCategory.homologyFunctor _ 0 ≅
      modulePushforward B S hS f :=
  have : PreservesFiniteLimits (modulePushforward B S hS f) :=
    have := (modulePullbackAdjunction B S hS f).rightAdjoint_preservesLimits
    inferInstance
  letI := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  haveI : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS f) RF α
  Stacks.DerivedFunctor.derivedZeroNatIso (modulePushforward B S hS f) RF α
    (isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f RF α)
    (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective _ _ _
      (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) J hJ)

end RightDerived

/-- **The canonical map `(f_*M)[0] ⟶ Rf_*(M[0])`** for the derived direct image
`AlgebraicGeometry.Space.derivedModulePushforward`: its unit
`AlgebraicGeometry.Space.derivedModulePushforwardUnit` at the complexes `M[0]`. -/
abbrev modulePushforwardSingleToDerived (f : X ⟶ Y) :
    modulePushforward B S hS f ⋙ DerivedCategory.singleFunctor _ 0 ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ derivedModulePushforward B S hS f :=
  modulePushforwardSingleToRightDerived B S hS f _ (derivedModulePushforwardUnit B S hS f)

/-- **`(f_*M)[0] ⟶ Rf_*(M[0])` is an isomorphism for affine `f` and quasi-coherent `M`.** -/
theorem isIso_modulePushforwardSingleToDerived_app_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((modulePushforwardSingleToDerived B S hS f).app M) :=
  isIso_modulePushforwardSingleToRightDerived_app_of_isAffineHom B S hS f _
    (derivedModulePushforwardUnit B S hS f) hf M hM

/-- **`Rf_*(M[0]) ≅ (f_*M)[0]` for an affine morphism `f` and a quasi-coherent module `M`**: the
inverse of the canonical map `AlgebraicGeometry.Space.modulePushforwardSingleToDerived`. -/
def derivedModulePushforwardSingleIsoOfIsAffineHom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS f).obj M) :=
  have := isIso_modulePushforwardSingleToDerived_app_of_isAffineHom B S hS f hf M hM
  (asIso ((modulePushforwardSingleToDerived B S hS f).app M)).symm

/-- **`Rf_*𝒪_X ≅ f_*𝒪_X` for an affine morphism `f`**, in `D(𝒪_Y)`: the inverse of the canonical
map `f_*𝒪_X ⟶ Rf_*𝒪_X`. -/
def derivedModulePushforwardStructureModuleIso (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) :
    (derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS f).obj
        (structureModule X)) :=
  derivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf _
    (SheafOfModules.isQuasicoherentOnSite_unit _)

/-- **`H⁰(Rf_*(M[0])) ≅ f_*M`, naturally in `M`,** for the derived direct image
`AlgebraicGeometry.Space.derivedModulePushforward` of any morphism `f` of algebraic spaces. -/
def derivedModulePushforwardSingleHomologyZeroIso (f : X ⟶ Y) :
    DerivedCategory.singleFunctor _ 0 ⋙ derivedModulePushforward B S hS f ⋙
        DerivedCategory.homologyFunctor _ 0 ≅ modulePushforward B S hS f :=
  rightDerivedModulePushforwardSingleHomologyZeroIso B S hS f _
    (derivedModulePushforwardUnit B S hS f)

end AlgebraicGeometry.Space

end
