module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject

/-!
# Compactly supported cohomology of a sheaf as `Ext` on the compactification

Let `f : X ⟶ Spec k` be separated of finite type, `j : X ⟶ X̄` a compactification over `k`, `Λ` a
commutative ring and `K` a sheaf of `Λ`-modules on `X_étale`. The compactly supported cohomology
`RΓ_c(X, K) = RΓ(Spec k, Rf_! K)` of Tag 0GJZ, with `Rf_! = R(f̄)_* ∘ Rj_!` (Tag 0F7H), is in each
degree an `Ext` group out of the constant sheaf on `X̄`:

`Hⁱ_c(X, K) ≅ Hⁱ(X̄, j_! K) ≅ Ext^i_X̄(Λ, j_! K)`.

The first isomorphism is that of
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIso` (extension by zero is exact,
and `Γ(X̄, -) = Γ(Spec k, -) ∘ f̄_*` with `f̄_*` preserving injectives), here read through the
derived global sections of `(j_! K)[0]`, so that the corepresentation of global sections by the
constant sheaf (`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt`) applies. This is the
form of `Hⁱ_c` on which the duality pairings of
`Stacks.EtaleCohomology.isDualityPerfect_of_dense_open_of_smooth` and
`Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTrace` are stated.

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIsoExt`:
  `Hⁱ_c(X, K) ≅ Ext^i_X̄(Λ, j_! K)`, read in abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

/-- **`Hⁱ_c(X, K) ≅ Ext^i_X̄(Λ, j_! K)`**, read in abelian groups, for a sheaf of modules `K`
placed in degree zero: compactly supported cohomology (Tag 0GJZ) is `Ext` out of the constant
sheaf on the compactification. -/
def compactlySupportedCohomologyGroupSingleIsoExt (K : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((compactlySupportedCohomologyGroup.{u, 0} k f j Λ (i : ℤ)).obj
          ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj K)) ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          j.space.smallEtaleTopology) i).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K) :=
  let e₁ := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).rightDerivedFunctorPlusObjSingleIso K
  let e₂ := (rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, 0} Λ j.toBase)
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of k)))
    (etaleModuleGlobalSections.{u, 0} Λ j.space)
    (etaleModuleGlobalSectionsDirectImageIso j.toBase Λ)).symm
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of k))).mapIso
            ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).mapIso e₁) ≪≫ e₂.app _)) ≪≫
    etaleModuleRightDerivedPlusIsoExt Λ _ _ i

end Stacks.EtaleCohomology
