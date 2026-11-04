module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseAConverse
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor

/-!
# Stacks 0D7M in case (A)

## Main results

* `CategoryTheory.SimplicialSite.CartesianSlice.isQuasicoherentOnSite_iff_isIso_transitionA`.
* `CategoryTheory.SimplicialSite.CartesianSlice.isQuasicoherentOnSite_iff_isCartesianModule_caseA`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})

/-- **Stacks 0D7M in case (A), with Mathlib's pullback along the transitions.** -/
theorem isQuasicoherentOnSite_iff_isIso_transitionA (F : SheafOfModules.{u} O) :
    F.IsQuasicoherentOnSite ↔
      (∀ (n m : SimplexCategory) (ψ : n ⟶ m), IsIso (transitionA C O ψ F)) ∧
        ∀ n : SimplexCategory,
          (((situation C).componentModuleRestriction O n).obj F).IsQuasicoherentOnSite :=
  ⟨fun hF => ⟨fun _ _ ψ => isIso_transitionA_of_isQuasicoherentOnSite C O ψ F hF,
      SimplicialSiteSituation.CartesianSlice.isQuasicoherentOnSite_componentModuleRestriction
        (situation C) O F hF⟩,
    fun h => SimplicialSiteSituation.CartesianSlice.isQuasicoherentOnSite_of_components
      (situation C) O F (fun ⟨⟨k⟩, x⟩ => ⟨k, x, rfl⟩) h.2
      fun n Q hQ => hasGlobalPresentation_over_of_isIso_transitionA C O Q F (h.1 n) hQ⟩

/-- In case (A), a module is cartesian exactly when its transitions for Mathlib's pullback along
`O(φ)` are invertible. -/
theorem isCartesianModule_iff_isIso_transitionA
    (P : Sheaf (situation C).totalTopology CommRingCat.{u})
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).IsCartesianModule P F ↔
      ∀ (n m : SimplexCategory) (ψ : n ⟶ m),
        IsIso (transitionA C (Stacks.SheafOfModules.Tensor.ringSheaf P) ψ F) := by
  refine forall_congr' fun n => forall_congr' fun m => forall_congr' fun ψ => ?_
  have : IsIso ((transitionPullbackModulesIsoA C P ψ).hom.app
      (((situation C).componentModuleRestriction
        (Stacks.SheafOfModules.Tensor.ringSheaf P) n).obj F)) :=
    Iso.isIso_hom ((transitionPullbackModulesIsoA C P ψ).app _)
  rw [fiberTransitionModules_eq_transitionA]
  exact @isIso_comp_left_iff _ _ _ _ _ _ _ this

/-- **Stacks 0D7M in case (A).** -/
theorem isQuasicoherentOnSite_iff_isCartesianModule_caseA
    (P : Sheaf (situation C).totalTopology CommRingCat.{u})
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    F.IsQuasicoherentOnSite ↔
      (situation C).IsCartesianModule P F ∧
        ∀ n : SimplexCategory, ((situation C).componentModule P F n).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isIso_transitionA C (Stacks.SheafOfModules.Tensor.ringSheaf P) F).trans
    (and_congr_left' (isCartesianModule_iff_isIso_transitionA C P F).symm)

end CategoryTheory.SimplicialSite.CartesianSlice
