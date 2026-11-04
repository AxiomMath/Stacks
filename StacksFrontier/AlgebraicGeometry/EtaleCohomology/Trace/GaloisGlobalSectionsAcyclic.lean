module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantDerivedGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# Acyclicity for `Γ^Gal` from acyclicity on `Y_K`

Let `k` be a field, `K/k` a separable algebraic extension and `Y` a quasi-compact and
quasi-separated `k`-scheme. A sheaf `H` of `Λ`-modules on `Y_étale` whose restriction to `Y_K` is
acyclic for `Γ(Y_K, -)` is acyclic for the Galois-equivariant global sections
`Γ^Gal : F ↦ Γ(Y_K, F|_{Y_K})` with values in discrete Galois modules. Forgetting the action,
`RΓ^Gal(H)` is `RΓ(Y_K, H|_{Y_K})` (`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso`),
whose higher cohomology vanishes, and the forgetful functor is exact and faithful.

This lets one compute `RΓ^Gal` on resolutions by sheaves that are only acyclic, such as
`ℋom(G, L)` with `L` injective.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_galoisGlobalSections_of_fieldBaseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius

universe w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisAcyclic (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules (Stacks 04JF), pinned at the module universe
`u + 1`. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisAcyclic (Λ : Type)
    [Ring Λ] (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λ)]

/-- **A sheaf whose restriction to `Y_K` is `Γ(Y_K, -)`-acyclic is `Γ^Gal`-acyclic.** -/
theorem rightAcyclic_galoisGlobalSections_of_fieldBaseChange (H : EtaleModules.{u, 0} Λ Y.left)
    (h : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightAcyclic
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj H)) :
    (galoisGlobalSections Λ Y kbar).rightAcyclic H := by
  let U := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)
  let res := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)
  have : U.Faithful :=
    ⟨fun h => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Action.hom_ext _ _ h))⟩
  have : U.ReflectsIsomorphisms := inferInstance
  have : PreservesFiniteLimits (galoisGlobalSections Λ Y kbar ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (res ⋙ Γ))
  have : PreservesFiniteLimits (galoisGlobalSections Λ Y kbar) :=
    preservesFiniteLimits_of_reflects_of_preserves _ U
  have hΓ := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus Γ
    (res.obj H)).2 inferInstance).1 h
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (galoisGlobalSections Λ Y kbar) H).2 inferInstance).2 fun i hi => ?_
  let Z := ((galoisGlobalSections Λ Y kbar).rightDerivedPlus i).obj H
  have hU : IsZero (U.obj Z) := (hΓ i hi).of_iso <|
    ((U.mapDerivedCategoryHomologyIso i).app (DerivedCategory.Plus.ι.obj
        ((galoisDerivedGlobalSections Λ Y kbar).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj H)))).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ i).mapIso
        ((galoisDerivedGlobalSectionsForgetIso Λ Y kbar).app _ ≪≫
          Γ.rightDerivedFunctorPlus.mapIso (Functor.mapDerivedCategoryPlusObjSingleIso res H))
  rw [IsZero.iff_id_eq_zero] at hU ⊢
  exact U.map_injective (by rw [U.map_id, hU, U.map_zero])

end Stacks.EtaleCohomology

end
