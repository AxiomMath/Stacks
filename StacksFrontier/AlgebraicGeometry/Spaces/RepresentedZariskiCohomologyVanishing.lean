module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Vanishing of the cohomology of a scheme read as an algebraic space

Let `U` be an object of the big fppf site over `S` and `𝒩` a quasi-coherent module on the small
étale site of the algebraic space `h_U` it represents.  If the Zariski cohomology
`Hⁿ(U, 𝒩|_{U_Zar})` vanishes, then so does the cohomology `Hⁿ(h_U, 𝒩)` of the algebraic space.

This is the direction of Stacks 03DW (`AlgebraicGeometry.Space.representedZariskiCohomologyIso`)
in which the proof of Stacks 0D39 uses it: Serre vanishing on the scheme fibre `X_y` is a
statement about Zariski cohomology, and the formal-functions argument runs on the small étale site
of the algebraic space `X`.  The two remaining crossings are formal: global sections of `h_U` are
the sections over the terminal chart cut out by `⊤`, and the Zariski cohomology of
`AlgebraicGeometry.Space.representedZariskiCohomologyIso` (derived functors of the module of
sections) and `Hgroup` (derived functors of the group of sections) differ by the exact forgetful
functor.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_isZero_Hgroup`: the vanishing.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The group of sections over an open of a sheaf of modules on a scheme is the underlying group
of its module of sections, naturally. -/
def secFIsoEvaluationForget (X : Scheme.{u}) (V : X.Opens) :
    secF X.ringCatSheaf V ≅ SheafOfModules.evaluation X.ringCatSheaf (op V) ⋙
      forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The cohomology of a scheme read as an algebraic space vanishes when its Zariski cohomology
does.**  Let `𝒩` be a quasi-coherent module on the small étale site of `h_U`.  If
`Hⁿ(U, 𝒩|_{U_Zar}) = 0` then `Hⁿ(h_U, 𝒩) = 0`. -/
theorem isZero_rightDerived_globalSections_of_isZero_Hgroup (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (n : ℕ)
    (h : IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ n
      (zariskiModule U N))) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)).rightDerived n).obj N) := by
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  refine isZero_rightDerived_globalSections_represented_of_isZero B S hS U N hN n ?_
  -- The Zariski cohomology of `ε_* 𝒩`, read in modules of sections.
  have hZ : IsZero (((SheafOfModules.evaluation.{u}
      (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤)).rightDerived n).obj
        ((representedZariskiDirectImage B S hS U).obj N)) := by
    have e₁ : (representedZariskiDirectImage B S hS U).obj N ≅ zariskiModule U N :=
      (restrictToChartSchemeIdEtaleChartIso B S hS U N ≪≫ selfOpensPushforwardIso B S hS U N).symm
    refine IsZero.of_iso ?_ ((((SheafOfModules.evaluation.{u}
      (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤)).rightDerived n).mapIso e₁))
    have h' : IsZero ((forget₂ (ModuleCat _) AddCommGrpCat).obj
        (((SheafOfModules.evaluation.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf
          (op ⊤)).rightDerived n).obj (zariskiModule U N))) :=
      h.of_iso (((Functor.rightDerivedCompIso (SheafOfModules.evaluation.{u}
          (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤)) (forget₂ _ AddCommGrpCat)
            n).app (zariskiModule U N)).symm ≪≫
        ((Functor.rightDerivedIsoOfNatIso
          (secFIsoEvaluationForget ((BigFppfOver.toScheme B S hS).obj U) ⊤) n).app
          (zariskiModule U N)).symm)
    rw [AddCommGrpCat.isZero_iff_subsingleton] at h'
    exact ModuleCat.isZero_of_subsingleton _
  exact hZ

end AlgebraicGeometry.Space

end
