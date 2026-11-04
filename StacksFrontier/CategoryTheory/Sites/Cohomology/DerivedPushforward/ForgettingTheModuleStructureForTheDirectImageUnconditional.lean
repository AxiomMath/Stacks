module
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage

public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructureUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertibleUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the module structure for the direct image, in general universes

For a continuous functor `w : D ⥤ C` between sites, where the sites need not be small and the
coefficients lie in any universe dominating the objects and morphisms of `C`, the degreewise
direct image along `w` takes a K-injective resolution of the underlying abelian complex of a
K-injective complex of modules to a quasi-isomorphism.

## Main results

* `Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective_univ`: the
  degreewise direct image of a K-injective resolution of the underlying abelian complex of a
  K-injective complex of modules is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open ModuleSheafCohomology
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.Cohomology.ForgetModule

universe v v₁ v₂ u₁ u₂ w

section General

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{v} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{v} B]

end General

section LargeSites

attribute [local instance] HasDerivedCategory.standard

universe t₀ u₃ v₃ u₄ v₄

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : D ⥤ C) [w.IsContinuous K J]
  [HasSheafify J AddCommGrpCat.{max u₃ v₃ t₀}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₃ v₃ t₀}]
  [HasSheafify K AddCommGrpCat.{max u₃ v₃ t₀}]

/-- **Degreewise direct image takes a K-injective resolution of the underlying abelian complex
of a K-injective complex of modules to a quasi-isomorphism**, on a site whose objects need not
form a small type and with coefficients in any universe dominating its objects and morphisms.
Quasi-isomorphy of a morphism of complexes of abelian sheaves is detected on the underlying
complexes of presheaves, hence object by object of the target site; sections over `V` of a
direct image are sections over `w(V)` on the nose; and those are corepresented by the free
abelian sheaf on `w(V)`, which is sectionwise torsion free, so the corepresentable criterion
applies with the bijectivity statement of parts (1) and (2) of Tag 0D6J as its input. -/
theorem quasiIso_abelianPushforward_map_of_isKInjective_univ
    (O : Sheaf J RingCat.{max u₃ v₃ t₀}) [EnoughInjectives (SheafOfModules.{max u₃ v₃ t₀} O)]
    (I : CochainComplex (SheafOfModules.{max u₃ v₃ t₀} O) ℤ) [I.IsKInjective]
    {Jc : CochainComplex (Sheaf J AddCommGrpCat.{max u₃ v₃ t₀}) ℤ} [Jc.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    [QuasiIso q] :
    QuasiIso (((w.sheafPushforwardContinuous AddCommGrpCat.{max u₃ v₃ t₀} K J).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  apply SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso_general K
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro s
  show QuasiIso ((((sheafSections J AddCommGrpCat.{max u₃ v₃ t₀}).obj
    (op (w.obj s.unop))).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  refine DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
    _ _ (FreeYonedaUnivLE.evaluationRepresentation.{t₀} J (w.obj s.unop)).symm q (fun n => ?_)
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max u₃ v₃ t₀}) (ComplexShape.up ℤ)).map
        (q⟦n⟧'))) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₃ v₃ t₀}) (ComplexShape.up ℤ))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    show QuasiIso ((CategoryTheory.shiftFunctor
      (CochainComplex (Sheaf J AddCommGrpCat.{max u₃ v₃ t₀}) ℤ) n).map q)
    infer_instance
  refine DerivedLowerShriek.bijective_postcomp_of_qh_bijective _
    (qh_map_bijective_single_of_isKInjective_general J O _
      (ModuleSheafCohomology.isTorsionFree_sheafify J
        (uliftYoneda.{max u₃ t₀}.obj (w.obj s.unop) ⋙ AddCommGrpCat.free) (fun W => by
          show Module.IsTorsionFree ℤ
            (FreeAbelianGroup (ULift.{max u₃ t₀} (W.unop ⟶ w.obj s.unop)))
          exact Module.Flat.isTorsionFree)) I n)
    (CochainComplex.IsKInjective.Qh_map_bijective _ (Jc⟦n⟧))

end LargeSites

section AbelianDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : D ⥤ C) [w.IsContinuous K J]

variable (O : Sheaf J RingCat.{u})

end AbelianDirectImage

section Pushforward

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

end Pushforward

end Stacks.Cohomology.ForgetModule

end
