module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTensorSingleSections

/-!
# Derived sections of a quasi-coherent module over an affine étale chart

Let `U` be an affine étale chart of an algebraic space `X` and `M` a quasi-coherent `𝒪_X`-module.
The derived sections `RΓ(U, M[0])` over the chart have no cohomology outside degree `0`: they are
the derived sections over the affine represented space `h_U` of the restriction `u^*(M[0])`
(`chartDerivedSectionsComparison`), whose cohomology is the sections of the cohomology sheaves
(`representedAffineDerivedSectionsHomologyIso`, quasi-coherent cohomology on an affine), and
`u^*(M[0])` has cohomology `u^*M` in degree `0` only.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_derivedSections_single`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasRightDerivedFunctor_chartSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
  (U : SmallEtale B S hS X.1)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))]

/-- **`Hⁱ(RΓ(U, M[0])) = 0` for `i ≠ 0`**, for a quasi-coherent `𝒪_X`-module `M` and an affine
étale chart `U` of `X`. -/
theorem isZero_homology_derivedSections_single (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M))) := by
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have hsingle : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M)) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor _ 0).obj M) 0 i h
    · exact DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor _ 0).obj M) 0 i h
  have hE := derivedQuasicoherent_etaleModulePullback B S hS (representedChartToSpace X U)
    (isEtale_representedChartToSpace X U) ((DerivedCategory.singleFunctor _ 0).obj M)
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS M hM)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) :=
    IsZero.of_iso (Functor.map_isZero (etaleModulePullback.{u, u} B S hS
        (representedChartToSpace X U) (isEtale_representedChartToSpace X U)) hsingle)
      (((etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)).mapDerivedCategoryHomologyIso i).app _)
  have h₂ := IsZero.of_iso (Functor.map_isZero (representedAffineSections B S hS T) h₁)
    (representedAffineDerivedSectionsHomologyIso B S hS T _ hE i)
  exact IsZero.of_iso h₂ ((DerivedCategory.homologyFunctor _ i).mapIso
    ((asIso (chartDerivedSectionsComparison X U)).app _))

end AlgebraicGeometry.Space

end
