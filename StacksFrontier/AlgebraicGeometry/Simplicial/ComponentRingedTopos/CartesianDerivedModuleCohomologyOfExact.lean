module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomology

/-!
# Stacks 0D7L (2) for exact face pullbacks

`isCartesianDerivedModule_iff_forall_isCartesianModule_homology` (Stacks 0D7L (2)) assumes the
morphisms of ringed topoi of the face maps flat, and uses that hypothesis only to make the
pullbacks of modules along them exact. This file states it with that exactness as the hypothesis.

## Main results

* `isCartesianDerivedModule_iff_forall_isCartesianModule_homology_of_preservesFiniteLimits`:
  if the face pullbacks of modules are exact, an object of `D(O)` is cartesian if and only if
  every cohomology module is cartesian.

## References

* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **Stacks 0D7L (2), for exact face pullbacks.** If the pullbacks of modules along the
morphisms of ringed topoi of the face maps are exact, an object `K` of `D(O)` is cartesian if and
only if every cohomology module `H^q(K)` is cartesian. -/
theorem isCartesianDerivedModule_iff_forall_isCartesianModule_homology_of_preservesFiniteLimits
    (exact : ∀ (k : ℕ) (i : Fin (k + 2)),
      PreservesFiniteLimits
        (S.transitionRingedToposHom O (SimplexCategory.δ i)).toModulesHom.pullbackModules)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.IsCartesianDerivedModule O K ↔
      ∀ q : ℤ, IsCartesianModule S O
        ((DerivedCategory.homologyFunctor (S.totalRingedTopos O).Modules q).obj K) := by
  have hface : ∀ (k : ℕ) (i : Fin (k + 2)),
      IsIso ((S.derivedComponentModuleTransition O (SimplexCategory.δ i)).app K) ↔
        ∀ q : ℤ, IsIso (S.fiberTransitionModules O (SimplexCategory.δ i)
          ((DerivedCategory.homologyFunctor (S.totalRingedTopos O).Modules q).obj K)) :=
    fun k i ↦ S.isIso_derivedComponentModuleTransition_app_iff O (SimplexCategory.δ i)
      (exact k i) K
  rw [S.isCartesianDerivedModule_iff_faces O K]
  exact ⟨fun h q ↦ (S.isCartesianModule_iff_faces O _).2 fun k i ↦ (hface k i).1 (h k i) q,
    fun h k i ↦ (hface k i).2 fun q ↦ (S.isCartesianModule_iff_faces O _).1 (h q) k i⟩

end CategoryTheory.SimplicialSiteSituation

end
