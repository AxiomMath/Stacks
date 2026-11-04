module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseACoherence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition

/-!
# The transition of case (A) read in the ringed-topos development

The cartesian condition of Stacks 07TF (2) is stated with the transitions of the morphisms of
ringed topoi of Stacks 09WF; this file identifies them, up to the comparison of the two pullbacks,
with the transitions for Mathlib's pullback along the ring maps `O(φ)` used in case (A).

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

variable (C : SimplicialSite.{u}) (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m)

/-- The direct-image transition of the ringed-topos development is the direct form of case (A),
followed by the comparison of the two direct images. -/
theorem restrictTransitionModulesApp_eq_directTransitionA
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).restrictTransitionModulesApp P φ F =
      (directTransitionA C (Stacks.SheafOfModules.Tensor.ringSheaf P) φ).app F ≫
        (transitionRingedToposPushforwardModulesIsoA C P φ).hom.app _ := by
  ext V : 3
  rfl

/-- The transition in the cartesian condition is the transition of case (A), up to the
comparison of the two pullbacks. -/
theorem fiberTransitionModules_eq_transitionA
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).fiberTransitionModules P φ F =
      (transitionPullbackModulesIsoA C P φ).hom.app _ ≫
        transitionA C (Stacks.SheafOfModules.Tensor.ringSheaf P) φ F := by
  refine (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv
    _ _).injective ?_
  refine ((situation C).fiberTransitionModules_adj P φ F).trans ?_
  refine (restrictTransitionModulesApp_eq_directTransitionA C P φ F).trans ?_
  refine Eq.trans ?_ (homEquiv_transitionPullbackModulesIsoA_hom_app_comp C P φ _ _ _).symm
  exact congrArg (· ≫ _) (((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (ringTransitionA C (Stacks.SheafOfModules.Tensor.ringSheaf P) φ)).homEquiv _ _).apply_symm_apply
      _).symm

end CategoryTheory.SimplicialSite.CartesianSlice
