module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushComponentFormula
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso

/-!
# Morphisms of quasi-coherent modules over an affine étale chart are linear maps of sections

Let `X` be an algebraic space, `A` an étale chart of `X` whose scheme is affine, and `M`, `N`
quasi-coherent `𝒪_X`-modules.  A morphism `α : M|_A ⟶ N|_A` of the restrictions to the slice of
the small étale site at `A` is determined by its component over the object of the slice that the
whole chart scheme cuts out, and every linear map of the sections there is such a component.

This is the space version of the statement that on an affine scheme a morphism out of a
quasi-coherent module is a linear map of global sections
(`Stacks.Algebraization.sectionsTop_bijective`, read through the Hom-set transport
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` and its component formula
`AlgebraicGeometry.Space.chartPushEquiv_chartSchemeModuleHomEquiv_apply`).

## Main results

* `AlgebraicGeometry.Space.eq_of_app_openChartOfComparisonOver_top`: two morphisms `M|_A ⟶ N|_A`
  with the same component over the whole chart are equal.
* `AlgebraicGeometry.Space.exists_app_openChartOfComparisonOver_top`: every linear map of the
  sections over the whole chart is the component of a morphism `M|_A ⟶ N|_A`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)

/-- The global sections of the chart restriction of a quasi-coherent module, read as its sections
over the étale chart that the whole chart scheme cuts out. -/
abbrev chartTopSections (A : SmallEtale B S hS X.1)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤)) :
    M.val.obj (op (openChartOfComparison B S hS X A ⊤)) :=
  chartPushEquiv B S hS X M A ⊤
    (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op ⊤)).hom x)

/-- The identification `AlgebraicGeometry.Space.chartTopSections` of the global sections of the
chart restriction with the sections over the whole chart is a bijection. -/
theorem chartTopSections_bijective (A : SmallEtale B S hS X.1) :
    Function.Bijective (chartTopSections B S hS X M hM A) :=
  (chartPushEquiv B S hS X M A ⊤).bijective.comp
    (SheafOfModules.bijective_hom_val_app_of_iso
      (chartSchemeModuleIsoChartPush B S hS X M hM A) (op ⊤))

/-- The identification of the global sections of the chart restriction with the sections over
the whole chart is semilinear over `AlgebraicGeometry.Space.chartSectionsRingHom`. -/
theorem chartTopSections_smul (A : SmallEtale B S hS X.1)
    (r : (chartScheme A).ringCatSheaf.obj.obj (op ⊤))
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤)) :
    chartTopSections B S hS X M hM A (r • x) =
      chartSectionsRingHom B S hS X A ⊤ r • chartTopSections B S hS X M hM A x :=
  (congrArg (chartPushEquiv B S hS X M A ⊤)
    (map_smul ((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op ⊤)).hom r x)).trans
    (chartPushEquiv_smul B S hS X M A ⊤ r _)

include hM hN in
/-- **A morphism of quasi-coherent modules over an affine étale chart is determined by its
component over the whole chart.** -/
theorem eq_of_app_openChartOfComparisonOver_top (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)] {α α' : M.over A ⟶ N.over A}
    (h : ∀ x : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤),
      (α.val.app (op (openChartOfComparisonOver B S hS X A ⊤))).hom
          (chartPushEquiv B S hS X M A ⊤
            (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op ⊤)).hom x)) =
        (α'.val.app (op (openChartOfComparisonOver B S hS X A ⊤))).hom
          (chartPushEquiv B S hS X M A ⊤
            (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op ⊤)).hom x))) :
    α = α' := by
  have := isQuasicoherent_chartSchemeModule B S hS X M hM A
  have key : ∀ x : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤),
      (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α).val.app (op ⊤)).hom x) =
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α').val.app (op ⊤)).hom x) := by
    intro x
    apply (chartTopSections_bijective B S hS X N hN A).1
    unfold chartTopSections
    rw [chartPushEquiv_chartSchemeModuleHomEquiv_apply B S hS X M N hM hN A α ⊤ x, h x,
      chartPushEquiv_chartSchemeModuleHomEquiv_apply B S hS X M N hM hN A α' ⊤ x]
  exact (chartSchemeModuleHomEquiv B S hS X M N hM hN A).injective
    ((Stacks.Algebraization.sectionsTop_bijective
      (chartSchemeModule B S hS X M hM A) (chartSchemeModule B S hS X N hN A)).1
      (LinearMap.ext key))

include hM hN in
/-- **Every linear map of the global sections of the chart restrictions is read off a morphism of
the restrictions of quasi-coherent modules to the slice at an affine étale chart**: its component
over the whole chart. -/
theorem exists_app_openChartOfComparisonOver_top (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)]
    (g : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤)
      →ₗ[(chartScheme A).ringCatSheaf.obj.obj (op ⊤)]
      (chartSchemeModule B S hS X N hN A).val.obj (op ⊤)) :
    ∃ α : M.over A ⟶ N.over A, ∀ x : (chartSchemeModule B S hS X M hM A).val.obj (op ⊤),
      (α.val.app (op (openChartOfComparisonOver B S hS X A ⊤))).hom
          (chartPushEquiv B S hS X M A ⊤
            (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op ⊤)).hom x)) =
        chartPushEquiv B S hS X N A ⊤
          (((chartSchemeModuleIsoChartPush B S hS X N hN A).hom.val.app (op ⊤)).hom (g x)) := by
  have := isQuasicoherent_chartSchemeModule B S hS X M hM A
  obtain ⟨β, hβ⟩ := (Stacks.Algebraization.sectionsTop_bijective
    (chartSchemeModule B S hS X M hM A) (chartSchemeModule B S hS X N hN A)).2 g
  refine ⟨(chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β, fun x => ?_⟩
  have hx : (β.val.app (op ⊤)).hom x = g x := LinearMap.congr_fun hβ x
  rw [chartPushEquiv_chartSchemeModuleHomEquiv_symm_apply B S hS X M N hM hN A β ⊤ x, hx]

end AlgebraicGeometry.Space

end
