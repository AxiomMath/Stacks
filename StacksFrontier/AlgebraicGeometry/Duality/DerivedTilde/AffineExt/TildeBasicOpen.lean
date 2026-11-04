module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.KInjectiveSections
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Sections over a principal open

Sections over `D(f)` of the sheaf `M̃` associated to an `R`-module `M` are `R_f ⊗_R M`,
naturally in `M`, and sections over `D(f)` of a K-injective complex of `𝒪_{Spec R}`-modules form a
K-injective complex of `R_f`-modules.

## Main results

* `AlgebraicGeometry.AffineExt.tildeBasicOpenNatIso`: the sections of `M̃` over `D(f)` are
  `R_f ⊗_R M`, naturally in `M`.
* `AlgebraicGeometry.AffineExt.isKInjective_sectionsS`: the sections over `D(f)` of a K-injective
  complex of `𝒪_{Spec R}`-modules form a K-injective complex of `R_f`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.AffineExt

variable (R : CommRingCat.{u})

/-- Sections over an open `U` of `Spec R`, as modules over `Γ(Spec R, U)`. -/
abbrev sectionsS (U : (Spec R).Opens) : (Spec R).Modules ⥤ ModuleCat.{u} Γ(Spec R, U) :=
  SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)

/-- Taking sections over `U` is an additive functor. -/
instance sectionsS_additive (U : (Spec R).Opens) : (sectionsS R U).Additive where
  map_add := rfl

/-- **Sections of `M̃` over `D(f)` are `M ⊗_R R_f`.** -/
def tildeBasicOpenIso (f : R) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (locMap R f).hom).obj M ≅
      (sectionsS R (basicOpen R f)).obj ((tilde.functor R).obj M) := by
  let S := locRing R f
  let X := (ModuleCat.restrictScalars (locMap R f).hom).obj (ModuleCat.of S S)
  have hst : IsScalarTower R S X := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e : X ≃ₗ[S] S := LinearEquiv.refl S S
  letI : Module S ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen R f))) :=
    ((sectionsS R (basicOpen R f)).obj ((tilde.functor R).obj M)).isModule
  haveI : IsScalarTower R S
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen R f))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso ≪≫
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) S
      (tilde.toOpen M (basicOpen R f)).hom).equiv.toModuleIso

/-- The isomorphism `tildeBasicOpenIso` sends `1 ⊗ m` to the section of `M̃` over `D(f)` defined
by `m`. -/
lemma tildeBasicOpenIso_hom_one_tmul (f : R) (M : ModuleCat.{u} R) (m : M) :
    (tildeBasicOpenIso R f M).hom ((1 : locRing R f) ⊗ₜ[R, (locMap R f).hom] m) =
      tilde.toOpen M (basicOpen R f) m := by
  let : Module (locRing R f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen R f))) :=
    ((sectionsS R (basicOpen R f)).obj ((tilde.functor R).obj M)).isModule
  have : IsScalarTower R (locRing R f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen R f))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact ((IsLocalizedModule.isBaseChange (Submonoid.powers f) (locRing R f)
    (tilde.toOpen M (basicOpen R f)).hom).equiv_tmul 1 m).trans (one_smul _ _)

/-- **Sections of `M̃` over `D(f)` are `M ⊗_R R_f`**, naturally in `M`. -/
def tildeBasicOpenNatIso (f : R) :
    ModuleCat.extendScalars (locMap R f).hom ≅ tilde.functor R ⋙ sectionsS R (basicOpen R f) :=
  NatIso.ofComponents (tildeBasicOpenIso R f) fun {M N} g => by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
    refine ((congrArg (tildeBasicOpenIso R f N).hom
      (ModuleCat.ExtendScalars.map_tmul _ g 1 m)).trans
        (tildeBasicOpenIso_hom_one_tmul R f N (g m))).trans ?_
    refine Eq.trans ?_ (congrArg ((tilde.functor R ⋙ sectionsS R (basicOpen R f)).map g).hom
      (tildeBasicOpenIso_hom_one_tmul R f M m)).symm
    exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app g (basicOpen R f)) m).symm

/-- Sections over `U` as `Γ(Spec R, U)`-modules, with scalars restricted to `R`, are sections over
`U` as `R`-modules. -/
def sectionsSRestrictIso (U : (Spec R).Opens) :
    sectionsS R U ⋙ ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom ≅
      TildeSlice.sectionsR U :=
  Iso.refl _

/-- Restriction of scalars along `R ⟶ R_f` is full: an `R`-linear map between `R_f`-modules is
`R_f`-linear. -/
instance full_restrictScalars_locMap (f : R) :
    (ModuleCat.restrictScalars.{u} (locMap R f).hom).Full where
  map_surjective {X Y} g := by
    let : Module R X := Module.compHom X (locMap R f).hom
    let : Module R Y := Module.compHom Y (locMap R f).hom
    have : IsScalarTower R (locRing R f) X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R (locRing R f) Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact ⟨ModuleCat.ofHom (LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f)
      (locRing R f) (show X →ₗ[R] Y from g.hom)), rfl⟩

/-- **Sections over `D(f)` of a K-injective complex are K-injective over `R_f`.** -/
theorem isKInjective_sectionsS (f : R) (I : CochainComplex (Spec R).Modules ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((sectionsS R (basicOpen R f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_of_fullyFaithful (ModuleCat.restrictScalars.{u} (locMap R f).hom)
    (fun _ hK => hK.map _) _ (show CochainComplex.IsKInjective
      (((ModuleCat.restrictScalars.{u} (locMap R f).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((sectionsS R (basicOpen R f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) from TildeSlice.isKInjective_sectionsR (basicOpen R f) I hI)

end AlgebraicGeometry.AffineExt
