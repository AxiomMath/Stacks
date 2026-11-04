module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyPushforwardOfVanishingHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource

/-!
# Cohomology of a module supported on a closed subscheme

Let `p : h_U ⟶ X` be a closed immersion of algebraic spaces from (the space of) a scheme `U`,
and `K` a quasi-coherent `𝒪_X`-module annihilated by the ideal of `p`.  Then `K = p_* p^* K`, and
since `p` is finite the cohomology of `K` on `X` is that of `p^* K` on `h_U`, which in turn is the
Zariski cohomology of `p^* K` on `U` (Stacks 03DW).  So `Hⁿ(X, K)` vanishes as soon as the Zariski
cohomology `Hⁿ(U, (p^* K)|_U)` does.

This is the passage, in the proof of Stacks 0D39, from the vanishing on the scheme fibre
`X_y` to the vanishing `Hᵖ(X, 𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ ⊗ ℒ^{⊗ d}) = 0` on `X`, there quoted as Cohomology of
Spaces, Lemma 0D2U.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_annihilatedByKerIdeal`: the
  vanishing.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Cohomology of a module killed by the ideal of a closed immersion from a scheme.**  Let
`p : h_U ⟶ X` be a closed immersion and `K` a quasi-coherent `𝒪_X`-module annihilated by the ideal
of `p`.  If the Zariski cohomology `Hⁿ(U, (p^* K)|_U)` vanishes, so does `Hⁿ(X, K)`. -/
theorem isZero_rightDerived_globalSections_of_annihilatedByKerIdeal {X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (p : schemeSpace U ⟶ X)
    (hp : IsClosedImmersion B S hS p.hom) (K : Modules.{u, u} B S hS X.1 X.2)
    (hK : AnnihilatedByKerIdeal B S hS p K) (hKqc : K.IsQuasicoherentOnSite) (n : ℕ)
    (h : IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ n
      (zariskiModule U ((modulePullback B S hS p).obj K)))) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj K) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have hunit : IsIso ((modulePullbackAdjunction B S hS p).unit.app K) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS p hp K).1
      (essImage_modulePushforward_of_annihilatedByKerIdeal B S hS p hp K hK)
  have hqc : ((modulePullback B S hS p).obj K).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS p K hKqc
  have hU := isZero_rightDerived_globalSections_of_isZero_Hgroup U _ hqc n h
  have hfin : IsFinite B S hS p.hom := isFinite_of_isClosedImmersion B S hS p.hom hp
  refine ((Functor.map_isZero (globalSectionsRestrictScalars B S hS p) hU).of_iso
    (cohomologyIsoOfIsFinite B S hS p hfin _ hqc n).symm).of_iso ?_
  exact ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).mapIso
    (@asIso _ _ _ _ _ hunit)

end AlgebraicGeometry.Space

end
