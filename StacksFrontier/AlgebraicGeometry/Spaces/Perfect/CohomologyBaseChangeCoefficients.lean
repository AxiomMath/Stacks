module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfIsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Coefficients for cohomology and base change: modules placed in degree zero

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  Cohomology and base change (Stacks 0A1P)
takes a bounded complex `G` of `𝒪_X`-modules whose terms are of finite presentation, flat over
`Y` and of support proper over `Y`.  This file checks these conditions for a module placed in
degree zero, in particular for `𝒪_X`, which is how Stacks 0CTM applies Stacks 0A1P.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_isProper_of_isClosed_support`: for proper `f`, every abelian sheaf
  with closed support has support proper over `Y`.
* `AlgebraicGeometry.Space.isFlatOver_structureSheafModule`: for flat `f`, `𝒪_X` is flat over
  `Y`.
* `𝒪_X` is of finite presentation by the instance
  `Stacks.SheafOfModules.Site.unit_isFinitePresentation`, since
  `AlgebraicGeometry.Space.structureSheafModule` is an abbreviation of `SheafOfModules.unit`.
* `AlgebraicGeometry.Space.isFlatOver_of_isZero`, `AlgebraicGeometry.Space.isFinitePresentation_of_isZero`:
  the zero terms of a module placed in degree zero satisfy the conditions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- For a proper morphism `f : X ⟶ Y`, an abelian sheaf on `X` with closed support has support
proper over `Y`. -/
theorem hasProperSupport_of_isProper_of_isClosed_support (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v})
    (hF : IsClosed (supportOfSheaf B S hS X.1 F)) :
    HasProperSupport B S hS X.2 Y.2 f.hom hft F :=
  ⟨hF, isProperOver_of_isProper B S hS X.2 Y.2 f.hom hft hf _ hF⟩

/-- For a proper morphism `f : X ⟶ Y`, the structure sheaf of `X` has support proper over `Y`. -/
theorem hasProperSupport_structureSheafModule (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f.hom) :
    HasProperSupport B S hS X.2 Y.2 f.hom hft
      ((SheafOfModules.toSheaf _).obj (structureSheafModule B S hS X)) :=
  hasProperSupport_of_isProper_of_isClosed_support B S hS f hf hft _
    ((supportOfSheaf_structureSheafModule B S hS X).symm ▸ isClosed_univ)

/-- For a flat morphism `f : X ⟶ Y`, the structure sheaf of `X` is flat over `Y`. -/
theorem isFlatOver_structureSheafModule (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom) :
    IsFlatOver B S hS X.2 f.hom (structureSheafModule B S hS X) :=
  (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f _).2
    ((isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule B S hS f).1 hfl)

/-- A zero `𝒪_X`-module is flat over `Y`: its geometric stalks vanish. -/
theorem isFlatOver_of_isZero (f : X ⟶ Y) {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsZero M) :
    IsFlatOver B S hS X.2 f.hom M := by
  have := SheafOfModules.IsQuasicoherentOnSite.of_isZero hM
  refine (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f M).2 fun x => ?_
  have : Subsingleton (geometricModuleStalk B S hS X x M) := by
    rw [← not_nontrivial_iff_subsingleton, nontrivial_geometricModuleStalk_iff]
    rintro ⟨N, s, hs⟩
    have : Subsingleton (M.val.obj (Opposite.op N.chart)) :=
      ModuleCat.isZero_iff_subsingleton.1
        ((SheafOfModules.evaluation _ (Opposite.op N.chart)).map_isZero hM)
    exact hs (by rw [Subsingleton.elim s 0, map_zero])
  unfold IsFlatOverAtGeometricPoint
  infer_instance

/-- A zero `𝒪_X`-module is of finite presentation: it is the cokernel of the identity of `𝒪_X`. -/
theorem isFinitePresentation_of_isZero {M : Modules.{u, u} B S hS X.1 X.2} (hM : IsZero M) :
    M.IsFinitePresentation :=
  have h := Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel
    (smallEtaleRingedSite B S hS X.1 X.2) (𝟙 (structureSheafModule B S hS X))
  (SheafOfModules.isFinitePresentation _).prop_of_iso
    ((isZero_cokernel_of_epi (𝟙 (structureSheafModule B S hS X))).iso hM) h

/-- For a proper morphism `f : X ⟶ Y`, an `𝒪_X`-module of finite presentation has support proper
over `Y`: its support is closed (Stacks 04KC). -/
theorem hasProperSupport_of_isFinitePresentation (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    [hM : M.IsFinitePresentation] :
    HasProperSupport B S hS X.2 Y.2 f.hom hft ((SheafOfModules.toSheaf _).obj M) :=
  have : SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) M := hM
  have : M.IsFinitePresentationOnSite :=
    Stacks.Sheaves.FinitePresentation.isFinitePresentationOnSite_of_isFinitePresentation
      (X := smallEtaleRingedTopos B S hS X) M
  hasProperSupport_of_isProper_of_isClosed_support B S hS f hf hft _
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 M)

end AlgebraicGeometry.Space
