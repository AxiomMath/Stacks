module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedPullbackSquare
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08GH: derived pullback and direct image of representable algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S`, with underlying morphism of
schemes `g_0 : X'_0 ⟶ X_0` and represented morphism of algebraic spaces `f : X' ⟶ X`.  This file
proves Stacks 08GH: under the equivalences `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` of Stacks 071Q,
`Lg_0^*` corresponds to `Lf^*`, and, for `f` quasi-compact and quasi-separated, `Rg_{0,*}`
corresponds to `Rf_*`.

The scheme-side functors are those of Stacks 08DW and 08D5, at the locally small model of
`D(𝒪_{X_0})` (`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`); the space-side ones are
those of Stacks 08F4 and 08FA.  The squares on the unbounded derived categories,
`AlgebraicGeometry.Space.representedZariskiToposDerivedPullbackCompIso` and its conjugate, are
stated with `g_0` read as a morphism of Zariski ringed topoi at the standard model; the
comparison with Stacks 08DW and 08D5 is `AlgebraicGeometry.Scheme.Hom.zariskiDerivedPullbackIso`
(the two are left derived functors of isomorphic functors) followed by
`StacksDraft.DerivedModel.derivedPullbackModelIso`, and likewise for direct images.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv`: `D_QCoh(𝒪_X)` at the standard and at
  the locally small model.
* `AlgebraicGeometry.Space.representedDualityQuasicoherentDerivedEquivalence`: Stacks 071Q for a
  representable algebraic space, at the locally small model of `D(𝒪_{X_0})`.
* `AlgebraicGeometry.Space.representedQuasicoherentDerivedPullbackIso` and
  `AlgebraicGeometry.Space.representedQuasicoherentDerivedPushforwardIso`: the two squares.

## Main results

* `AlgebraicGeometry.Space.nonempty_representedQuasicoherentDerivedPullbackIso_and_pushforwardIso`:
  Stacks 08GH.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace StacksDraft.DerivedModel

universe v w

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **The comparison of the standard and the locally small model commutes with cohomology**:
`H^n` of the locally small model, after the comparison, is `H^n` of the standard model. -/
def grothendieckModelEquivHomologyIso (n : ℤ) :
    (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor ⋙
        @DerivedCategory.homologyFunctor C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) n ≅
      @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard C) n :=
  letI := HasDerivedCategory.standard C
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      ((Stacks.Injectives.grothendieckModelEquiv.{w} C).functor ⋙
        @DerivedCategory.homologyFunctor C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      @DerivedCategory.homologyFunctorFactors C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) n⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (DerivedCategory.homologyFunctor C n) :=
    ⟨DerivedCategory.homologyFunctorFactors C n⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) _ _ (Iso.refl _)

end StacksDraft.DerivedModel

namespace Stacks.Duality

/-- **`D_QCoh(𝒪_X)` at the standard model is `D_QCoh(𝒪_X)` at the locally small model**: the
comparison of the two models of `D(𝒪_X)` preserves the cohomology sheaves. -/
def quasiCoherentDerivedCategoryModelEquiv (X : AlgebraicGeometry.Scheme.{u}) :
    @quasiCoherentDerivedCategory X (HasDerivedCategory.standard X.Modules) ≌
      quasiCoherentDerivedCategory X :=
  haveI : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
    ⟨fun e hE n => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e) (hE n)⟩
  (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).congrFullSubcategory (by
    ext E
    exact ⟨fun h n => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso X.Modules n).app E) (h n),
      fun h n => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso X.Modules n).app E).symm
          (h n)⟩)

end Stacks.Duality

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived pullback along a morphism of schemes read as a morphism of Zariski ringed topoi
exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_zariskiRingedToposHom :
    (pullbackOnHomotopy (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
      f.zariskiRingedToposHom).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y.zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
    f.zariskiRingedToposHom

/-- `zariskiPullbackModulesIsoSchemeModules` with the pullback of modules of ringed spaces as
target. -/
def zariskiPullbackModulesIsoModulePullback :
    f.zariskiRingedToposHom.toModulesHom.pullbackModules ≅
      RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom :=
  f.zariskiPullbackModulesIsoSchemeModules

/-- Degreewise pullback along `f` read as a morphism of Zariski ringed topoi is degreewise pullback
along `f` read as a morphism of ringed spaces. -/
def zariskiPullbackOnHomotopyIso :
    pullbackOnHomotopy (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        f.zariskiRingedToposHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f.toLRSHom.toShHom :=
  Functor.isoWhiskerRight (@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
    (RingedToposHom.pullbackModules_additive f.zariskiRingedToposHom)
    (RingedSpaceModuleAdjunction.modulePullback_additive f.toLRSHom.toShHom)
    f.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ)) DerivedCategory.Qh

omit f in
/-- The localization functor of `D(𝒪_Y)` at the standard model, at the Zariski-topos spelling. -/
theorem isLocalization_zariskiQh (Y : Scheme.{u}) :
    (@DerivedCategory.Qh (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.zariskiRingedTopos.J)
          Y.zariskiRingedTopos.O))) _ _
        (HasDerivedCategory.standard _)).IsLocalization
      (quasiIsoTarget (Y := Y.zariskiRingedTopos)) :=
  inferInstance

/-- Derived pullback along `f` read as a morphism of ringed spaces is a left derived functor of
degreewise pullback along `f` read as a morphism of ringed spaces, as a functor out of the homotopy
category of `𝒪_Y`-modules spelled through the Zariski ringed topos. -/
theorem isLeftDerivedFunctor_derivedPullback_zariski :
    @Functor.IsLeftDerivedFunctor _ _ _ _ _ _
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom) _
      (@DerivedCategory.Qh (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.zariskiRingedTopos.J)
          Y.zariskiRingedTopos.O))) _ _
        (HasDerivedCategory.standard _))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom) (quasiIsoTarget (Y := Y.zariskiRingedTopos))
      (isLocalization_zariskiQh Y) :=
  have h : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).IsLeftDerivedFunctor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom) (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (ComplexShape.up ℤ)) :=
    inferInstance
  @Functor.IsLeftDerivedFunctor.mk _ _ _ _ _ _ _ _ _ _ _ (isLocalization_zariskiQh Y) h.1

/-- Derived pullback along `f` read as a morphism of Zariski ringed topoi is derived pullback
along `f` read as a morphism of ringed spaces, both at the standard model. -/
def zariskiDerivedPullbackIso :
    derivedPullback (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        f.zariskiRingedToposHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom :=
  @Functor.leftDerivedNatIso _ _ _ _ _ _ _ _ _ _ _
    (derivedPullbackComparison (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        f.zariskiRingedToposHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f.toLRSHom.toShHom)
    (quasiIsoTarget (Y := Y.zariskiRingedTopos)) (isLocalization_zariskiQh Y)
    (isLeftDerivedFunctor_derivedPullback_zariski f) inferInstance (zariskiPullbackOnHomotopyIso f)

/-- **Derived pullback along `f` read as a morphism of Zariski ringed topoi, at the standard
model, is `Lf^*` of Stacks 08DW at the locally small model**, up to the comparison of models. -/
def zariskiDerivedPullbackModelIso :
    derivedPullback (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        f.zariskiRingedToposHom ⋙ (StacksDraft.DerivedModel.schemeModulesComparison X).functor ≅
      (StacksDraft.DerivedModel.schemeModulesComparison Y).functor ⋙
        Stacks.Duality.derivedPullback f :=
  Functor.isoWhiskerRight (zariskiDerivedPullbackIso f) _ ≪≫
    StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom

/-- `zariskiPushforwardModulesIsoSchemeModules` with the direct image of modules of ringed
spaces as target. -/
def zariskiPushforwardModulesIsoModulePushforward :
    f.zariskiRingedToposHom.pushforwardModules ≅
      RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom :=
  f.zariskiPushforwardModulesIsoSchemeModules

/-- Degreewise direct image along `f` read as a morphism of Zariski ringed topoi is degreewise
direct image along `f` read as a morphism of ringed spaces. -/
def zariskiPushforwardOnHomotopyIso :
    Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy (X := X.zariskiRingedTopos)
        (Y := Y.zariskiRingedTopos) f.zariskiRingedToposHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory
        f.toLRSHom.toShHom :=
  Functor.isoWhiskerRight (@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
    (RingedToposHom.pushforwardModules_additive f.zariskiRingedToposHom)
    (RingedSpaceModuleAdjunction.modulePushforward_additive f.toLRSHom.toShHom)
    f.zariskiPushforwardModulesIsoModulePushforward (ComplexShape.up ℤ)) DerivedCategory.Qh

omit f in
/-- The localization functor of `D(𝒪_X)` at the standard model, at the Zariski-topos spelling,
is a localization at the quasi-isomorphisms of the source spelling. -/
theorem isLocalization_zariskiQh_source (X : Scheme.{u}) :
    (@DerivedCategory.Qh (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.zariskiRingedTopos.J)
          X.zariskiRingedTopos.O))) _ _
        (HasDerivedCategory.standard _)).IsLocalization
      (Stacks.Cohomology.DerivedPushforward.sourceQuasiIso X.zariskiRingedTopos) :=
  inferInstance

/-- Derived direct image along `f` read as a morphism of ringed spaces is a right derived functor
of degreewise direct image, as a functor out of the homotopy category of `𝒪_X`-modules spelled
through the Zariski ringed topos. -/
theorem isRightDerivedFunctor_derivedPushforward_zariski :
    @Functor.IsRightDerivedFunctor _ _ _ _ _ _
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom) _
      (@DerivedCategory.Qh (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.zariskiRingedTopos.J)
          X.zariskiRingedTopos.O))) _ _
        (HasDerivedCategory.standard _))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedPushforward.sourceQuasiIso X.zariskiRingedTopos)
      (isLocalization_zariskiQh_source X) :=
  have h : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      f.toLRSHom.toShHom).IsRightDerivedFunctor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
        f.toLRSHom.toShHom) (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) :=
    inferInstance
  @Functor.IsRightDerivedFunctor.mk _ _ _ _ _ _ _ _ _ _ _ (isLocalization_zariskiQh_source X) h.1

/-- Derived direct image along `f` read as a morphism of Zariski ringed topoi is derived direct
image along `f` read as a morphism of ringed spaces, both at the standard model. -/
def zariskiDerivedPushforwardIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X.zariskiRingedTopos)
        (Y := Y.zariskiRingedTopos) f.zariskiRingedToposHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom :=
  @Functor.rightDerivedNatIso _ _ _ _ _ _ _ _ _ _ _
    ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy (X := X.zariskiRingedTopos)
        (Y := Y.zariskiRingedTopos) f.zariskiRingedToposHom).totalRightDerivedUnit
        DerivedCategory.Qh
        (Stacks.Cohomology.DerivedPushforward.sourceQuasiIso X.zariskiRingedTopos))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
      f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedPushforward.sourceQuasiIso X.zariskiRingedTopos)
    (isLocalization_zariskiQh_source X) inferInstance
    (isRightDerivedFunctor_derivedPushforward_zariski f) (zariskiPushforwardOnHomotopyIso f)

/-- **Derived direct image along `f` read as a morphism of Zariski ringed topoi, at the standard
model, is `Rf_*` at the locally small model**, up to the comparison of models. -/
def zariskiDerivedPushforwardModelIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X.zariskiRingedTopos)
        (Y := Y.zariskiRingedTopos) f.zariskiRingedToposHom ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison Y).functor ≅
      (StacksDraft.DerivedModel.schemeModulesComparison X).functor ⋙
        @Stacks.Duality.derivedPushforward X Y f (Scheme.Modules.hasDerivedCategory X)
          (Scheme.Modules.hasDerivedCategory Y) :=
  Functor.isoWhiskerRight (zariskiDerivedPushforwardIso f) _ ≪≫
    StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom

end

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 071Q for a representable algebraic space, at the locally small model of
`D(𝒪_{X_0})`**: the equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` of Stacks 08GH and 0E6E. -/
def representedDualityQuasicoherentDerivedEquivalence (T : BigFppfOver B S hS) :
    Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
        (representedSpace T).2 :=
  (Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).symm.trans
    (representedZariskiQuasicoherentDerivedEquivalence B S hS T)

variable {B S hS} {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The first square of Stacks 08GH on the unbounded derived categories, with `D(𝒪_{X_0})` at the
locally small model: `Lε_T^* ⋙ Lf^* ≅ Lg_0^* ⋙ Lε_{T'}^*` after the comparison of models. -/
def representedDerivedPullbackSquareIso :
    (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).inverse ⋙
        representedZariskiDerivedPullback B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      Stacks.Duality.derivedPullback (B.inclusion.map g.left) ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse ⋙
        representedZariskiDerivedPullback B S hS T' :=
  Functor.isoWhiskerLeft _ (representedZariskiToposDerivedPullbackCompIso B S hS g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((CatCommSq.hInv
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))
      (derivedPullback
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom)
      (Stacks.Duality.derivedPullback (B.inclusion.map g.left))
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T'))
      ⟨((B.inclusion.map g.left).zariskiDerivedPullbackModelIso).symm⟩).iso) _ ≪≫
    Functor.associator _ _ _

/-- The second square of Stacks 08GH on the unbounded derived categories, precomposed with
`Lε_{T'}^*`: `Lε_{T'}^* ⋙ Rf_* ⋙ Rε_{T,*} ≅ Lε_{T'}^* ⋙ Rε_{T',*} ⋙ Rg_{0,*}`. -/
def representedDerivedPushforwardSquareIso :
    representedZariskiDerivedPullback B S hS T' ⋙
        derivedModulePushforward B S hS (representedSpaceMap B S hS g) ⋙
        representedZariskiDerivedPushforward B S hS T ≅
      representedZariskiDerivedPullback B S hS T' ⋙ representedZariskiDerivedPushforward B S hS T' ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom :=
  Functor.isoWhiskerLeft _ (representedZariskiToposDerivedPushforwardCompIso B S hS g)

/-- `Rg_{0,*}` at the locally small model, conjugated by the comparison of models, is `Rg_{0,*}`
read as a morphism of Zariski ringed topoi at the standard model. -/
def representedDerivedPushforwardModelIso :
    (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).functor ≅
      @Stacks.Duality.derivedPushforward _ _ (B.inclusion.map g.left)
        (Scheme.Modules.hasDerivedCategory _) (Scheme.Modules.hasDerivedCategory _) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((CatCommSq.hInv
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T'))
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom)
      (@Stacks.Duality.derivedPushforward _ _ (B.inclusion.map g.left)
        (Scheme.Modules.hasDerivedCategory _) (Scheme.Modules.hasDerivedCategory _))
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))
      ⟨((B.inclusion.map g.left).zariskiDerivedPushforwardModelIso).symm⟩).iso) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).counitIso ≪≫
    Functor.rightUnitor _

end

/-- The equivalence of `representedDualityQuasicoherentDerivedEquivalence`, followed by the
inclusion of `D_QCoh(𝒪_X)`, is the inclusion of `D_QCoh(𝒪_{X_0})` followed by the comparison
of models and `Lε^*`. -/
def representedQuasicoherentDerivedEquivalenceFunctorCompιIso (U : BigFppfOver B S hS) :
    (representedDualityQuasicoherentDerivedEquivalence B S hS U).functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse ⋙
        representedZariskiDerivedPullback B S hS U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
    Functor.associator _ _ _

/-- **Stacks 08GH, the first square**: for a morphism `g : T' ⟶ T` of the big fppf site over
`S`, with underlying morphism of schemes `g_0` and represented morphism of algebraic spaces `f`,
`Lg_0^* : D_QCoh(𝒪_{X_0}) ⥤ D_QCoh(𝒪_{X'_0})` and `Lf^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X'})` correspond
under the equivalences of Stacks 071Q. -/
def representedQuasicoherentDerivedPullbackIso :
    Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left) ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ⋙
        quasicoherentDerivedModulePullback (representedSpaceMap B S hS g) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (representedQuasicoherentDerivedEquivalenceFunctorCompιIso T') ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (representedDerivedPullbackSquareIso g).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (representedQuasicoherentDerivedEquivalenceFunctorCompιIso T).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (quasicoherentDerivedModulePullbackCompιIso
        (representedSpaceMap B S hS g)).symm ≪≫
      (Functor.associator _ _ _).symm)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- `Lε^*` on `D_QCoh`, followed by the inclusion, is the inclusion followed by `Lε^*`. -/
def representedZariskiQuasicoherentDerivedPullbackCompιIso (U : BigFppfOver B S hS) :
    representedZariskiQuasicoherentDerivedPullback B S hS U ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ representedZariskiDerivedPullback B S hS U :=
  ObjectProperty.liftCompιIso _ _ _

/-- `Rε_*` on `D_QCoh`, followed by the inclusion, is the inclusion followed by `Rε_*`. -/
def representedZariskiQuasicoherentDerivedPushforwardCompιIso (U : BigFppfOver B S hS) :
    representedZariskiQuasicoherentDerivedPushforward B S hS U ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ representedZariskiDerivedPushforward B S hS U :=
  ObjectProperty.liftCompιIso _ _ _

/-- On `D_QCoh(𝒪_{X_0})` at the standard model, `Lε^* ⋙ Rε_*` is the identity: the unit of the
equivalence of Stacks 071Q. -/
def representedZariskiQuasicoherentUnitIso (U : BigFppfOver B S hS) :
    (ObjectProperty.ι _ :
        Stacks.Duality.quasiCoherentDerivedCategory
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U) ⥤ _) ⋙
        representedZariskiDerivedPullback B S hS U ⋙ representedZariskiDerivedPushforward B S hS U ≅
      ObjectProperty.ι _ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedZariskiQuasicoherentDerivedPullbackCompιIso U).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (representedZariskiQuasicoherentDerivedEquivalence B S hS U).functor
      (representedZariskiQuasicoherentDerivedPushforwardCompιIso U).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (representedZariskiQuasicoherentDerivedEquivalence B S hS U).unitIso.symm _ ≪≫
    Functor.leftUnitor _

variable (hfqc : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom)
  (hfqs : IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom)

/-- **The second square of Stacks 08GH at the standard model of `D(𝒪_{X_0})`**: on
`D_QCoh(𝒪_{X'_0})`, `Rg_{0,*}` (with `g_0` read as a morphism of Zariski ringed topoi) is the
conjugate of `Rf_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_X)` by the equivalences of Stacks 071Q. -/
def representedZariskiQuasicoherentDerivedPushforwardSquareIso :
    (ObjectProperty.ι _ :
        Stacks.Duality.quasiCoherentDerivedCategory
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T') ⥤ _) ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom ≅
      ((representedZariskiQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs ⋙
        (representedZariskiQuasicoherentDerivedEquivalence B S hS T).inverse) ⋙
        ObjectProperty.ι _ :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (representedZariskiQuasicoherentUnitIso T').symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (representedDerivedPushforwardSquareIso g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedZariskiQuasicoherentDerivedPullbackCompιIso T').symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quasicoherentDerivedPushforwardCompιIso B S hS
        (representedSpaceMap B S hS g) hfqc hfqs).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (representedZariskiQuasicoherentDerivedPushforwardCompιIso T).symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

end

end AlgebraicGeometry.Space

namespace Stacks.Duality

/-- The comparison of models on `D_QCoh`, followed by the inclusion, is the inclusion followed by
the comparison of models. -/
def quasiCoherentDerivedCategoryModelEquivFunctorCompιIso (X : AlgebraicGeometry.Scheme.{u}) :
    (quasiCoherentDerivedCategoryModelEquiv X).functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ (StacksDraft.DerivedModel.schemeModulesComparison X).functor :=
  ObjectProperty.liftCompιIso _ _ _

/-- The inverse comparison of models on `D_QCoh`, followed by the inclusion, is the inclusion
followed by the inverse comparison of models. -/
def quasiCoherentDerivedCategoryModelEquivInverseCompιIso (X : AlgebraicGeometry.Scheme.{u}) :
    (quasiCoherentDerivedCategoryModelEquiv X).inverse ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ (StacksDraft.DerivedModel.schemeModulesComparison X).inverse :=
  ObjectProperty.liftCompιIso _ _ _

end Stacks.Duality

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' T : BigFppfOver B S hS}
  (g : T' ⟶ T)

variable (hfqc : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom)
  (hfqs : IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom)

/-- `Rg_{0,*}` at the locally small model on `D_QCoh(𝒪_{X'_0})`, read at the standard model. -/
def representedQuasicoherentDerivedPushforwardModelIso :
    (ObjectProperty.ι _ :
        Stacks.Duality.quasiCoherentDerivedCategory
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T') ⥤ _) ⋙
        Stacks.Duality.derivedPushforward (B.inclusion.map g.left) ≅
      (Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse ⋙
        (ObjectProperty.ι _ ⋙
          Stacks.Cohomology.DerivedPushforward.derivedPushforward
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
            (B.inclusion.map g.left).zariskiRingedToposHom) ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).functor :=
  Functor.isoWhiskerLeft _ (representedDerivedPushforwardModelIso g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.Duality.quasiCoherentDerivedCategoryModelEquivInverseCompιIso
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

/-- **The second square of Stacks 08GH on the inclusion of `D_QCoh`**: on `D_QCoh(𝒪_{X'_0})` at the
locally small model, `Rg_{0,*}` is the conjugate of `Rf_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_X)` by the
equivalences of Stacks 071Q. -/
def representedQuasicoherentDerivedPushforwardSquareIso :
    (ObjectProperty.ι _ :
        Stacks.Duality.quasiCoherentDerivedCategory
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T') ⥤ _) ⋙
        Stacks.Duality.derivedPushforward (B.inclusion.map g.left) ≅
      ((representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse) ⋙
        ObjectProperty.ι _ :=
  representedQuasicoherentDerivedPushforwardModelIso g ≪≫
    Functor.isoWhiskerLeft
      (Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse
      (Functor.isoWhiskerRight
          (representedZariskiQuasicoherentDerivedPushforwardSquareIso g hfqc hfqs)
          (StacksDraft.DerivedModel.schemeModulesComparison
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).functor ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          ((representedZariskiQuasicoherentDerivedEquivalence B S hS T').functor ⋙
            quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs ⋙
            (representedZariskiQuasicoherentDerivedEquivalence B S hS T).inverse)
          (Stacks.Duality.quasiCoherentDerivedCategoryModelEquivFunctorCompιIso
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).symm)

include hfqc hfqs in
/-- `Rg_{0,*}` carries `D_QCoh(𝒪_{X'_0})` into `D_QCoh(𝒪_{X_0})` when the represented morphism of
algebraic spaces is quasi-compact and quasi-separated. -/
theorem isQuasicoherent_homology_derivedPushforward_representedSchemeMap
    (K : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T')) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.Scheme.Modules
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) i).obj
      ((Stacks.Duality.derivedPushforward (B.inclusion.map g.left)).obj K.obj)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.Scheme.Modules
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) i).mapIso
      ((representedQuasicoherentDerivedPushforwardSquareIso g hfqc hfqs).app K).symm)
    ((((representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse).obj K).property i)

/-- A functor `F : D_QCoh(𝒪_{X'_0}) ⥤ D_QCoh(𝒪_{X_0})` lifting `Rg_{0,*}` is the conjugate of
`Rf_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_X)` by the equivalences of Stacks 071Q. -/
def representedQuasicoherentDerivedPushforwardIsoOfCompιIso
    (F : Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T') ⥤
      Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))
    (e : F ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Stacks.Duality.derivedPushforward (B.inclusion.map g.left)) :
    F ⋙ (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs :=
  Functor.isoWhiskerRight (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
      (e ≪≫ representedQuasicoherentDerivedPushforwardSquareIso g hfqc hfqs)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).counitIso ≪≫
      Functor.rightUnitor _)

/-- **Stacks 08GH, the second square**: for a morphism `g : T' ⟶ T` of the big fppf site over `S`
whose represented morphism of algebraic spaces `f` is quasi-compact and quasi-separated, with
underlying morphism of schemes `g_0`, `Rg_{0,*} : D_QCoh(𝒪_{X'_0}) ⥤ D_QCoh(𝒪_{X_0})` and
`Rf_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_X)` correspond under the equivalences of Stacks 071Q. -/
def representedQuasicoherentDerivedPushforwardIso :
    Stacks.Duality.quasiCoherentDerivedPushforward (B.inclusion.map g.left)
        (isQuasicoherent_homology_derivedPushforward_representedSchemeMap g hfqc hfqs) ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs :=
  representedQuasicoherentDerivedPushforwardIsoOfCompιIso g hfqc hfqs _
    (ObjectProperty.liftCompιIso _ _ _)

omit hfqc hfqs in
/-- **Stacks 08GH.** Let `g : T' ⟶ T` be a morphism of the big fppf site over `S`, so that
`f = h_g : X' ⟶ X` is a morphism of representable algebraic spaces represented by the morphism of
schemes `g_0 : X'_0 ⟶ X_0`.  Under the equivalences `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` of
Stacks 071Q,

1. `Lg_0^* : D_QCoh(𝒪_{X_0}) ⥤ D_QCoh(𝒪_{X'_0})` corresponds to
   `Lf^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X'})`, and
2. if `f` is quasi-compact and quasi-separated, `Rg_{0,*} : D_QCoh(𝒪_{X'_0}) ⥤ D_QCoh(𝒪_{X_0})`
   corresponds to `Rf_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 08GH]
theorem nonempty_representedQuasicoherentDerivedPullbackIso_and_pushforwardIso :
    Nonempty (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left) ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ⋙
        quasicoherentDerivedModulePullback (representedSpaceMap B S hS g)) ∧
    ∀ (hfqc : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom)
      (hfqs : IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom),
      Nonempty (Stacks.Duality.quasiCoherentDerivedPushforward (B.inclusion.map g.left)
          (isQuasicoherent_homology_derivedPushforward_representedSchemeMap g hfqc hfqs) ⋙
          (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ≅
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
          quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs) :=
  ⟨⟨representedQuasicoherentDerivedPullbackIso g⟩,
    fun hfqc hfqs => ⟨representedQuasicoherentDerivedPushforwardIso g hfqc hfqs⟩⟩

end AlgebraicGeometry.Space
