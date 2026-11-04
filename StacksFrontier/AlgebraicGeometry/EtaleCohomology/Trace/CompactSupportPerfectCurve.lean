module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstructibleCurveCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the cohomology of constructible torsion sheaves on proper curves, read through
`Rg_*` and `RΓ(Spec k, -)`

For a proper scheme `Y` of dimension at most one over an algebraically closed field `k` and a
constructible torsion sheaf `G` of modules over a Noetherian ring `Λ`, the cohomology of
`RΓ(Spec k, Rg_* G)` is finite in every nonnegative degree: it is `Hⁿ(Y, G)`, finite by
[Stacks, Tag 0GJK]. This is the shape of the finiteness input of the perfectness criterion
`Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_finite`
for the perfectness of `RΓ_c` of a flat sheaf on a curve ([Stacks, Tag 03V3]).

## Main results

* `Stacks.EtaleCohomology.module_finite_homology_derivedDirectImageSections_of_isProper`

## References

* [Stacks Project, Tag 0GJK](https://stacks.math.columbia.edu/tag/0GJK)
* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`Hⁿ(RΓ(Spec k, Rg_* G))` is finite** for a constructible torsion sheaf `G` of modules over a
Noetherian ring on a proper scheme `Y` of dimension at most one over an algebraically closed field
`k`, in every degree `n ≥ 0` (Tag 0GJK). -/
@[sga "4 XVII 5.3.6" "special case", sga "5 I 3.1.6" "clause a), special case"]
theorem module_finite_homology_derivedDirectImageSections_of_isProper {k : Type u} [Field k]
    [IsAlgClosed k] (B : BigEtaleSite.{u}) (Y : B.Scheme) (g : Y.obj ⟶ Spec (.of k))
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [IsProper g]
    (hdim : topologicalKrullDim Y.obj ≤ 1) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (G : EtaleModules.{u, 0} Λ Y.obj) (hc : IsBigSiteConstructibleEtaleModule B Y Λ G)
    (ht : IsTorsionEtaleModule.{u, 0} Λ Y.obj G) (n : ℕ) :
    Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).obj
      (derivedDirectImageSections g Λ G)) := by
  have h := TorsionModules.module_finite_etaleCohomology_of_isProper B Y g hdim Λ G hc ht n
  let e : ((etaleModuleGlobalSections.{u, 0} Λ Y.obj).rightDerived n).obj G ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).obj
        (derivedDirectImageSections g Λ G) :=
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} Λ Y.obj) n).app G) ≪≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).mapIso
        (derivedDirectImageSectionsIsoDerivedGlobalSections Λ g G)).symm
  exact Module.Finite.equiv e.toLinearEquiv

end Stacks.EtaleCohomology

end
