module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonSituation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageQcqs
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePicard

/-!
# Higher direct images of the structure sheaf along a morphism of schemes, read on spaces

Let `g : T ⟶ U` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
`r` is quasi-compact and quasi-separated. Read `g` as a morphism of algebraic spaces
`yoneda.obj T ⟶ yoneda.obj U` (`AlgebraicGeometry.schemeSpaceMap`). This file shows that the
higher direct images `Rⁿ g_*𝒪` of the structure sheaf along the direct image of Stacks 03LU, on
the small étale site of the algebraic space `yoneda.obj U`, are the modules associated with the
Zariski higher direct images `Rⁿ r_*𝒪_T`, carried across the identification of the small étale
site of `yoneda.obj U` with the small étale site of the scheme underlying `U`.

## Main results

* `AlgebraicGeometry.Space.rightDerivedModulePushforwardSchemeSpaceMapStructureSheafModuleIso`:
  `Rⁿ g_*𝒪_{yoneda.obj T} ≅ ((Rⁿ r_*𝒪_T)ᵃ)` read on the small étale site of `yoneda.obj U`.

## The route

1. The structure sheaf of `yoneda.obj T` is the reading of the structure sheaf of the small
   étale site of the scheme underlying `T`, on the nose.
2. Right derived functors are transported along the identifications of module categories
   (`CategoryTheory.Functor.rightDerivedObjIsoOfEquivalence`), the two direct images agreeing
   across them by `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.
3. The structure sheaf of the small étale site of a scheme is the associated module of `𝒪`
   (`AlgebraicGeometry.SmallEtale.associatedModuleObjUnitIso`), and the étale clause of
   Stacks 071N (`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso`) computes
   the higher direct images of an associated module along a qcqs morphism.

## Implementation notes

The direct image of Stacks 03LU is stated along `AlgebraicGeometry.schemeSpaceMap`, not along
its unfolding `AlgebraicGeometry.Space.representedSpaceMap`: with the latter the source and target
algebraic spaces are anonymous constructors, and instance search no longer finds
`AlgebraicGeometry.Space.modulePushforward_additive`. Inside the proof the additivity and the
preservation of finite limits of that direct image are passed explicitly for the same reason.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {T U : BigFppfOver B S hS}
  (g : T ⟶ U)

/-- **The higher direct images of the structure sheaf along a morphism of schemes, read on the
algebraic spaces, are the associated modules of the Zariski higher direct images.** For a
morphism `g : T ⟶ U` of the big fppf site whose underlying morphism of schemes `r` is
quasi-compact and quasi-separated, `Rⁿ g_*𝒪_{yoneda.obj T}`, for the direct image of Stacks 03LU
along `yoneda.obj T ⟶ yoneda.obj U`, is the module `(Rⁿ r_*𝒪_T)ᵃ` on the small étale site of the
scheme underlying `U`, read on the small étale site of `yoneda.obj U` (Stacks 071N). -/
def rightDerivedModulePushforwardSchemeSpaceMapStructureSheafModuleIso
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map g)] (n : ℕ) :
    haveI := hasInjectiveResolutions_modules B S hS (schemeSpace T).1 (schemeSpace T).2
    ((modulePushforward B S hS (schemeSpaceMap g)).rightDerived n).obj
        (structureSheafModule B S hS (schemeSpace T)) ≅
      representedSmallEtaleModule B S hS U
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived n).obj
            (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf))) :=
  haveI : QuasiCompact (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) :=
    ‹QuasiCompact ((BigFppfOver.toScheme B S hS).map g)›
  haveI : QuasiSeparated (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) :=
    ‹QuasiSeparated ((BigFppfOver.toScheme B S hS).map g)›
  haveI : EnoughInjectives (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :=
    enoughInjectives_modules B S hS _ _
  haveI : EnoughInjectives (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (smallEtaleRingedSite_isGrothendieckAbelian (associatedBigEtaleSite B) _ T.left.property _)
  haveI : HasInjectiveResolutions
      (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :=
    ⟨fun _ => inferInstance⟩
  haveI : (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).Additive :=
    ⟨rfl⟩
  haveI : (representedSmallEtaleModuleEquivalence B S hS T).functor.Additive := ⟨rfl⟩
  haveI : (representedSmallEtaleModuleEquivalence B S hS U).functor.Additive := ⟨rfl⟩
  have hpfl : PreservesFiniteLimits (modulePushforward B S hS (schemeSpaceMap g)) :=
    have := (modulePullbackAdjunction B S hS (schemeSpaceMap g)).rightAdjoint_preservesLimits
    inferInstance
  (@Functor.rightDerivedObjIsoOfEquivalence _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS U)
    (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g))
    (modulePushforward B S hS (schemeSpaceMap g)) _ (modulePushforward_additive B S hS _) hpfl _ _
    (representedModulePushforwardSquareIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
    (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)) n).symm ≪≫
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
    (((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).rightDerived
        n).mapIso
      (SmallEtale.associatedModuleObjUnitIso (associatedBigEtaleSite B) _ T.left.property).symm ≪≫
    SmallEtale.higherDirectImageAssociatedModuleObjIso (associatedBigEtaleSite B) g.left
      (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf) n)

end AlgebraicGeometry.Space
