module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbeddingUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap

/-!
# ItemAuxiliaryUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section Torsion

variable {X : Scheme.{u}}

/-- **An abelian sheaf on `X_étale` killed by `n` embeds in the underlying abelian sheaf of an
injective sheaf of `ℤ/nℤ`-modules.** Being killed by `n`, it is the underlying sheaf of a sheaf
of `ℤ/nℤ`-modules (`Stacks.Cohomology.ZModSheaf.torsionSheafToModules`), and sheaves of modules
on the small étale site have enough injectives. -/
public theorem exists_mono_toSheaf_injective_univ (n : ℕ)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hA : n • 𝟙 A = 0) :
    ∃ (J : SheafOfModules.{max (u + 1) v}
        (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) (_ : Injective J)
      (i : A ⟶ (SheafOfModules.toSheaf _).obj J), Mono i := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, v}
    (J := X.smallEtaleTopology)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, v}
    (J := X.smallEtaleTopology)
  have : EnoughInjectives (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, max (u + 1) v, v} _
  have hA' : ∀ (U : X.Etaleᵒᵖ) (x : ToType (A.obj.obj U)), n • x = 0 := by
    intro U x
    rw [← natCast_zsmul]
    refine (zsmul_id_eq_zero_iff A n).1 ?_ U x
    rw [natCast_zsmul]
    exact hA
  set M := torsionSheafToModules.{max (u + 1) v, max (u + 1) v} X.smallEtaleTopology n A hA'
  exact ⟨Injective.under M, inferInstance,
    (torsionSheafToModulesIso.{max (u + 1) v, max (u + 1) v} X.smallEtaleTopology n A hA').inv ≫
      (SheafOfModules.toSheaf _).map (Injective.ι M), inferInstance⟩

end Torsion

section Negative

variable {Y Z Y' Z' : Scheme.{u}}

end Negative

end Stacks.EtaleCohomology

namespace Stacks.Cohomology.GlobalKunneth

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction derivedPushforwardCompIso)

attribute [local instance 10000] HasDerivedCategory.standard

section PullbackMapFunctoriality

variable {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V)

end PullbackMapFunctoriality

end Stacks.Cohomology.GlobalKunneth

end
