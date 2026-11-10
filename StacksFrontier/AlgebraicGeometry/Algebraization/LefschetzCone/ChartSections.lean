module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Isomorphism
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections

/-!
# Sections of a graded module's sheaf on a chart of the projective scheme

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L` such that the canonical morphism
`f : X ⟶ Proj Γ_*(X, L)` of Stacks 01PZ is an isomorphism, as it is for `X` proper over a field
(Stacks 0EKI). For a graded `Γ_*(X, L)`-module `M` and a homogeneous `a` of positive degree, the
sections of `f^* M̃` over the nonvanishing open `X_a = f⁻¹ D₊(a)` are the degree-zero localization
`M₍a₎` (Stacks 01M7). This file records that identification together with its two
compatibilities: it is semilinear along the chart ring map `Γ_*(X, L)₍a₎ → Γ(X_a, 𝒪_X)` of
Stacks 01PZ, and it is natural in `M`.

## Main definitions

* `Stacks.LefschetzCone.restrictedTilde`: the module `f^* M̃ = M̃|_X` on `X`.
* `Stacks.LefschetzCone.chartSections`: the identification `Γ(X_a, f^* M̃) ≃ M₍a₎`.

## Main results

* `Stacks.LefschetzCone.injective_chartRingMap`: the chart ring map is injective.
* `Stacks.LefschetzCone.chartSections_smul`: `chartSections` is semilinear.
* `Stacks.LefschetzCone.coe_chartSections_map`: `chartSections` is natural in `M`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (GoodChart associatedSchemeFunctor image_nvOpen)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.LefschetzCone

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- **The module `f^* M̃ = M̃|_X`** attached to a graded `Γ_*(X, L)`-module. -/
abbrev restrictedTilde (M : GradedModuleCat.{u, u, u} (grading L)) : X.Modules :=
  ((associatedSchemeFunctor L).obj M).restrict (projHomOfIsAmple L hL)

/-- `M ↦ f^* M̃` as a functor. -/
abbrev restrictedTildeFunctor : GradedModuleCat.{u, u, u} (grading L) ⥤ X.Modules :=
  associatedSchemeFunctor L ⋙ Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)

omit [IsOpenImmersion (projHomOfIsAmple L hL)] in
include hL in
/-- **The chart ring map is injective** when the canonical morphism is an isomorphism: it is the
ring map of the isomorphism on the sections over `D₊(a)`, preceded by the bijection
`Γ_*(X, L)₍a₎ ≅ Γ(D₊(a), 𝒪)`. -/
public theorem injective_chartRingMap [IsIso (projHomOfIsAmple L hL)] {d : ℕ}
    (a : powSections L d) (hd : 0 < d) :
    Function.Injective
      (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a))) := by
  intro y y' h
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd
  have key : ∀ z, (projHomOfIsAmple L hL).app
      (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a))
      (Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) z) =
        X.presheaf.map (homOfLE hpre.le).op
          (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a)) z) := by
    intro z
    rw [Stacks.SectionRingProjQuasicoherent.app_awayToSection L hL a hd hpre.le]
    exact (Stacks.SectionRingChartOpen.map_chartRingMap L a le_rfl hpre.le hpre.le z).symm
  have h1 := (key y).trans ((congrArg _ h).trans (key y').symm)
  have hinj₁ : Function.Injective ((projHomOfIsAmple L hL).app
      (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hinj₂ : Function.Injective
      (Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a)) := by
    have := ProjectiveSpectrum.Proj.isIso_awayToSection (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) hd
    exact (ConcreteCategory.bijective_of_isIso _).1
  exact hinj₂ (hinj₁ h1)

/-- A homogeneous element of positive degree, as a chart of `Proj A` inside the image of the
canonical morphism, which is everything when that morphism is an isomorphism. -/
abbrev goodChartOf [IsIso (projHomOfIsAmple L hL)] {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    GoodChart L hL :=
  ⟨⟨d, hd, a⟩, by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top⟩

/-- **The sections of `f^* M̃` over a chart `X_a` are `M₍a₎`.** -/
def chartSections (M : GradedModuleCat.{u, u, u} (grading L)) (c : GoodChart L hL) :
    Γ(restrictedTilde L hL M, nvOpen L c.1.val) ≃+
      GradedModuleDegreeZeroLocalization (grading L) M.grade
        (DirectSum.of (powSections L) c.1.deg c.1.val) :=
  (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
      ((associatedSchemeFunctor L).obj M) (nvOpen L c.1.val) _
      (image_nvOpen L hL c)).addCommGroupIsoToAddEquiv.trans
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L) M.grade
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos).toAddEquiv

/-- `chartSections` sends a section over `X_a` to the image, under the identification of sections
of `M̃` over `D₊(a)` with `M₍a₎`, of the corresponding section of `M̃` over `D₊(a)`. -/
theorem chartSections_apply (M : GradedModuleCat.{u, u, u} (grading L)) (c : GoodChart L hL)
    (x : Γ(restrictedTilde L hL M, nvOpen L c.1.val)) :
    chartSections L hL M c x =
      ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L) M.grade
        (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
        ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
          ((associatedSchemeFunctor L).obj M) (nvOpen L c.1.val) _
          (image_nvOpen L hL c)).hom x) := rfl


/-- The function on `D₊(a)` that a function on `X_a` comes from is the image of the fraction the
chart ring map sends to it. -/
public theorem awayToSection_eq_of_chartRingMap [IsIso (projHomOfIsAmple L hL)]
    (c : GoodChart L hL)
    (y : HomogeneousLocalization.Away (grading L)
      (DirectSum.of (powSections L) c.1.deg c.1.val)) :
    Proj.awayToSection (grading L) (DirectSum.of (powSections L) c.1.deg c.1.val) y =
      (AlgebraicGeometry.Proj (grading L)).presheaf.map (eqToHom (image_nvOpen L hL c).symm).op
        (((projHomOfIsAmple L hL).appIso (nvOpen L c.1.val)).inv
          (Stacks.SectionRingChartMap.chartRingMap L c.1.val le_rfl y)) := by
  obtain ⟨y', hy'⟩ := ProjectiveSpectrum.Proj.surjective_awayToSection (grading L)
    (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
    ((AlgebraicGeometry.Proj (grading L)).presheaf.map (eqToHom (image_nvOpen L hL c).symm).op
      (((projHomOfIsAmple L hL).appIso (nvOpen L c.1.val)).inv
        (Stacks.SectionRingChartMap.chartRingMap L c.1.val le_rfl y)))
  have h4 := Stacks.SectionRingProjQuasicoherent.chartRingMap_eq_of_awayToSection L hL c _ y' hy'
  have hyy : y' = y := injective_chartRingMap L hL c.1.val c.1.deg_pos h4
  exact (congrArg (Proj.awayToSection (grading L)
    (DirectSum.of (powSections L) c.1.deg c.1.val)) hyy.symm).trans hy'

/-- **`chartSections` is semilinear along the chart ring map.** -/
public theorem chartSections_smul [IsIso (projHomOfIsAmple L hL)]
    (M : GradedModuleCat.{u, u, u} (grading L)) (c : GoodChart L hL)
    (y : HomogeneousLocalization.Away (grading L)
      (DirectSum.of (powSections L) c.1.deg c.1.val))
    (x : Γ(restrictedTilde L hL M, nvOpen L c.1.val)) :
    chartSections L hL M c
        (Stacks.SectionRingChartMap.chartRingMap L c.1.val le_rfl y • x) =
      y • chartSections L hL M c x := by
  have h1 := ProjectiveSpectrum.Proj.imageSectionsIso_smul (projHomOfIsAmple L hL)
    ((associatedSchemeFunctor L).obj M) (nvOpen L c.1.val) _ (image_nvOpen L hL c)
    (Stacks.SectionRingChartMap.chartRingMap L c.1.val le_rfl y) x
  rw [← awayToSection_eq_of_chartRingMap L hL c y] at h1
  exact (chartSections_apply L hL M c _).trans ((congrArg _ h1).trans (map_smul _ y _))

/-- **`chartSections` is natural in the graded module**: read in the ambient localization, the map
induced by a degree-preserving `φ : M ⟶ N` on sections over `X_a` is the localization of `φ`. -/
public theorem coe_chartSections_map {M N : GradedModuleCat.{u, u, u} (grading L)}
    (φ : M ⟶ N) (c : GoodChart L hL) (x : Γ(restrictedTilde L hL M, nvOpen L c.1.val)) :
    (chartSections L hL N c (((restrictedTildeFunctor L hL).map φ).app _ x) :
        LocalizedModule.Away (DirectSum.of (powSections L) c.1.deg c.1.val) N.carrier) =
      LocalizedModule.map (Submonoid.powers (DirectSum.of (powSections L) c.1.deg c.1.val))
        φ.toLinearMap (chartSections L hL M c x :
          LocalizedModule.Away (DirectSum.of (powSections L) c.1.deg c.1.val) M.carrier) := by
  have hnat : (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        ((associatedSchemeFunctor L).obj N) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom
        (((restrictedTildeFunctor L hL).map φ).app _ x) =
      ((associatedSchemeFunctor L).map φ).app _
        ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
          ((associatedSchemeFunctor L).obj M) (nvOpen L c.1.val) _
          (image_nvOpen L hL c)).hom x) := by
    change ((associatedSchemeFunctor L).obj N).presheaf.map _
        (((associatedSchemeFunctor L).map φ).app _ x) =
      ((associatedSchemeFunctor L).map φ).app _
        (((associatedSchemeFunctor L).obj M).presheaf.map _ x)
    exact (ConcreteCategory.congr_hom
      (((associatedSchemeFunctor L).map φ).mapPresheaf.naturality _) x).symm
  have hstd := associatedModuleSheafMap_standardOpen (grading L) M.grade N.grade φ.toLinearMap
    φ.map_grade (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
    ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
      ((associatedSchemeFunctor L).obj M) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom x)
  refine Eq.trans ?_ hstd
  exact congrArg (fun t => ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
    (grading L) N.grade (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos t :
      GradedModuleDegreeZeroLocalization (grading L) N.grade _) :
        LocalizedModule.Away (DirectSum.of (powSections L) c.1.deg c.1.val) N.carrier)) hnat

/-! ### The same, indexed by the homogeneous element -/

variable [IsIso (projHomOfIsAmple L hL)]

/-- **The sections of `f^* M̃` over `X_a` are `M₍a₎`**, for `a` homogeneous of positive degree. -/
def chartSectionsOf (M : GradedModuleCat.{u, u, u} (grading L)) {d : ℕ} (a : powSections L d)
    (hd : 0 < d) :
    Γ(restrictedTilde L hL M, nvOpen L a) ≃+
      GradedModuleDegreeZeroLocalization (grading L) M.grade (DirectSum.of (powSections L) d a) :=
  chartSections L hL M (goodChartOf L hL a hd)

/-- `chartSectionsOf` is semilinear along the chart ring map. -/
public theorem chartSectionsOf_smul (M : GradedModuleCat.{u, u, u} (grading L)) {d : ℕ}
    (a : powSections L d) (hd : 0 < d)
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a))
    (x : Γ(restrictedTilde L hL M, nvOpen L a)) :
    chartSectionsOf L hL M a hd (Stacks.SectionRingChartMap.chartRingMap L a le_rfl y • x) =
      y • chartSectionsOf L hL M a hd x :=
  chartSections_smul L hL M (goodChartOf L hL a hd) y x

/-- `chartSectionsOf` is natural in the graded module. -/
public theorem coe_chartSectionsOf_map {M N : GradedModuleCat.{u, u, u} (grading L)}
    (φ : M ⟶ N) {d : ℕ} (a : powSections L d) (hd : 0 < d)
    (x : Γ(restrictedTilde L hL M, nvOpen L a)) :
    (chartSectionsOf L hL N a hd (((restrictedTildeFunctor L hL).map φ).app _ x) :
        LocalizedModule.Away (DirectSum.of (powSections L) d a) N.carrier) =
      LocalizedModule.map (Submonoid.powers (DirectSum.of (powSections L) d a))
        φ.toLinearMap (chartSectionsOf L hL M a hd x :
          LocalizedModule.Away (DirectSum.of (powSections L) d a) M.carrier) :=
  coe_chartSections_map L hL φ (goodChartOf L hL a hd) x

end Monoidal

end Stacks.LefschetzCone

end
