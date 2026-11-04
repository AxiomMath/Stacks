module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback

/-!
# Further results on `FlatSingleDerivedPullback`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

universe w₁ w₂ u

namespace Stacks.Cohomology.FlatSingleDerivedPullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived pullback of a flat module placed in degree zero.** For `F` a flat
`𝒪_Y`-module, `Lf^*(F[0])` is the degreewise pullback `f^*F` placed in degree `0`: the complex
`F[0]` is K-flat, so the comparison `Lf^* ⟶ f^*` is invertible on it.

The derived categories of `X` and `Y` may be taken in arbitrary models, not necessarily
`CategoryTheory.HasDerivedCategory.standard`, as in
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`, which this consumes: nothing in the
argument depends on the model, and the statement is needed at the locally small model of
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
def derivedPullbackSingleIsoAtModel
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj F) := by
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF 0)
  exact (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) 0).app F) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0).app
      ((modulePullback f).obj F)).symm

end Stacks.Cohomology.FlatSingleDerivedPullback

end
