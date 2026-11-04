module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomSquare
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransportApp
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The squares of Stacks 08GH on complexes

The first square of Stacks 08GH,
`AlgebraicGeometry.Space.representedDerivedPullbackSquareIso`, is assembled from the composition
isomorphisms of Stacks 0D6D, the comparison of the derived pullback along a morphism of schemes
read on Zariski ringed topoi and on ringed spaces, and the comparison of the standard and the
locally small model. This file computes it on complexes: after the comparisons of the derived
pullbacks with degreewise pullback it is the class of a degreewise isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.zariskiDerivedPullbackModelIso_hom_app_comparison`
* `AlgebraicGeometry.Space.representedZariskiToposDerivedPullbackCompIso_hom_app_comparison`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Stacks.Duality

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The comparison of `Lf^*` of Stacks 08DW with degreewise pullback, in the scheme spelling. -/
abbrev derivedPullbackComparison :
    (DerivedCategory.Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
        DerivedCategory Y.Modules) ⋙ derivedPullback f ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f.toLRSHom.toShHom

/-- **Stacks 0D5S on complexes, at the locally small model**: the composition isomorphism of
derived pullbacks, followed by the comparison for the composite, is the comparison for `f₂`,
then the one for `f₁`, then the degreewise composition isomorphism. -/
theorem derivedPullbackCompIso_hom_app_comparison {Z : AlgebraicGeometry.Scheme.{u}} (f₂ : Y ⟶ Z)
    (W : HomotopyCategory Z.Modules (ComplexShape.up ℤ)) :
    (derivedPullbackCompIso f f₂).hom.app (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ f₂)).app W =
      (derivedPullback f).map ((derivedPullbackComparison f₂).app W) ≫
        (derivedPullbackComparison f).app
          (((AlgebraicGeometry.Scheme.Modules.pullback f₂).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso
          f.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app W) := by
  have : (derivedPullback (f ≫ f₂)).IsLeftDerivedFunctor (derivedPullbackComparison (f ≫ f₂))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    inferInstanceAs ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (f ≫ f₂).toLRSHom.toShHom).IsLeftDerivedFunctor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison _)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
        (ComplexShape.up ℤ)))
  exact (Functor.leftDerived_fac_app (derivedPullback (f ≫ f₂)) (derivedPullbackComparison (f ≫ f₂))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (derivedPullback f₂ ⋙ derivedPullback f)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit f.toLRSHom.toShHom
        f₂.toLRSHom.toShHom (derivedPullback f) (derivedPullback f₂)
        (derivedPullbackComparison f) (derivedPullbackComparison f₂)) W).trans
    (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app f.toLRSHom.toShHom
      f₂.toLRSHom.toShHom (derivedPullback f) (derivedPullback f₂)
      (derivedPullbackComparison f) (derivedPullbackComparison f₂) W)

end Stacks.Duality

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The component of `zariskiDerivedPullbackModelIso` at `E` is the comparison
`zariskiDerivedPullbackIso` at `E`, transported along `schemeModulesComparison`, followed by
`derivedPullbackModelIso` at `E`. -/
theorem zariskiDerivedPullbackModelIso_hom_app
    (E : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.zariskiRingedTopos.J)
        Y.zariskiRingedTopos.O)))) :
    f.zariskiDerivedPullbackModelIso.hom.app E =
      (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
          (f.zariskiDerivedPullbackIso.hom.app E) ≫
        (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app E :=
  rfl

/-- `zariskiDerivedPullbackModelIso` on complexes. -/
theorem zariskiDerivedPullbackModelIso_hom_app_comparison
    (K : HomotopyCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.zariskiRingedTopos.J)
        Y.zariskiRingedTopos.O))) (ComplexShape.up ℤ)) :
    f.zariskiDerivedPullbackModelIso.hom.app (DerivedCategory.Qh.obj K) ≫
        (Stacks.Duality.derivedPullback f).map
          ((StacksDraft.DerivedModel.shrinkComparisonQhIso Y.Modules).inv.app K) ≫
        (Stacks.Duality.derivedPullbackComparison f).app K =
      (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
          ((derivedPullbackComparison (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
            f.zariskiRingedToposHom).app K ≫ (f.zariskiPullbackOnHomotopyIso).hom.app K) ≫
        (StacksDraft.DerivedModel.shrinkComparisonQhIso X.Modules).inv.app
          (((Scheme.Modules.pullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  have h₁ : f.zariskiDerivedPullbackIso.hom.app (DerivedCategory.Qh.obj K) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom).app K =
      (derivedPullbackComparison (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        f.zariskiRingedToposHom).app K ≫ (f.zariskiPullbackOnHomotopyIso).hom.app K :=
    @Functor.leftDerivedNatTrans_app _ _ _ _ _ _ _ _ _ _ _ _ _
      (quasiIsoTarget (Y := Y.zariskiRingedTopos)) (isLocalization_zariskiQh Y)
      (isLeftDerivedFunctor_derivedPullback_zariski f) _ K
  have h₂ := StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_comparison_whiskerLeft
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
      (ComplexShape.up ℤ)) _
    (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison _ _
      f.toLRSHom.toShHom (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      inferInstance)
    (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison _ _
      f.toLRSHom.toShHom
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))).symm
    (StacksDraft.DerivedModel.shrinkComparisonQhIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).symm K
  refine (eq_whisker (zariskiDerivedPullbackModelIso_hom_app f _) _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ h₂).trans ?_))
  exact (Functor.map_comp_assoc _ _ _ _).symm.trans
    (eq_whisker (congrArg (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map h₁) _)

end

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' T : BigFppfOver B S hS}
  (g : T' ⟶ T)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- `representedZariskiToposDerivedPullbackCompIso` is the composition isomorphism of derived
pullbacks through the small étale topos of `T`, followed by the isomorphism of derived pullbacks
induced by `representedZariskiPullbackModulesCompIso`, followed by the inverse of the composition
isomorphism through the Zariski topos of `T'`. -/
theorem representedZariskiToposDerivedPullbackCompIso_eq :
    representedZariskiToposDerivedPullbackCompIso B S hS g =
      derivedPullbackCompIso (X := smallEtaleRingedTopos B S hS (representedSpace T'))
          (Y := smallEtaleRingedTopos B S hS (representedSpace T))
          (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (X := smallEtaleRingedTopos B S hS (representedSpace T'))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (representedZariskiPullbackModulesCompIso B S hS g) ≪≫
        (derivedPullbackCompIso (X := smallEtaleRingedTopos B S hS (representedSpace T'))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
          (B.inclusion.map g.left).zariskiRingedToposHom).symm :=
  rfl

/-- **The first square of Stacks 08GH at the Zariski topos, on complexes.** -/
theorem representedZariskiToposDerivedPullbackCompIso_hom_app_comparison
    (K : HomotopyCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))
      (ComplexShape.up ℤ)) :
    (representedZariskiToposDerivedPullbackCompIso B S hS g).hom.app (DerivedCategory.Qh.obj K) ≫
        (representedZariskiDerivedPullback B S hS T').map
          ((derivedPullbackComparison
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
            (B.inclusion.map g.left).zariskiRingedToposHom).app K) ≫
        (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace T'))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
            (B.inclusion.map g.left).zariskiRingedToposHom).obj K) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace T))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)).app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (X := smallEtaleRingedTopos B S hS (representedSpace T))
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
            (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
          (B.inclusion.map g.left).zariskiRingedToposHom
          (representedZariskiPullbackModulesCompIso B S hS g)).hom.app K) :=
  eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (derivedPullbackSquareIso_hom_app_comparison
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (B.inclusion.map g.left).zariskiRingedToposHom
      (representedZariskiPullbackModulesCompIso B S hS g) K)) (by heq_congr)))

/-- The first square of Stacks 08GH at the locally small model, at an object coming from the
standard model, is the square at the Zariski topos followed by the comparison of the derived
pullbacks along the underlying morphism of schemes. -/
theorem representedDerivedPullbackSquareIso_hom_app_functor_obj
    (Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))) :
    (representedDerivedPullbackSquareIso g).hom.app
        ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).functor.obj Y) ≫
      (representedZariskiDerivedPullback B S hS T').map
        ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse.map
          ((B.inclusion.map g.left).zariskiDerivedPullbackModelIso.inv.app Y)) ≫
      (representedZariskiDerivedPullback B S hS T').map
        ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).unitInv.app
          ((derivedPullback
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
            (B.inclusion.map g.left).zariskiRingedToposHom).obj Y)) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedZariskiDerivedPullback B S hS T).map
            ((StacksDraft.DerivedModel.schemeModulesComparison
              (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).unitInv.app Y)) ≫
        (representedZariskiToposDerivedPullbackCompIso B S hS g).hom.app Y :=
  StacksDraft.DerivedModel.hInv_paste_hom_app _ _ _ _
    ⟨((B.inclusion.map g.left).zariskiDerivedPullbackModelIso).symm⟩ _ _ _ _ Y

end

end AlgebraicGeometry.Space
