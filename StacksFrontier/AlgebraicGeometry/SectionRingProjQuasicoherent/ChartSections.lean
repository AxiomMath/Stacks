module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.StandardOpenNaturality
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.ChartLinearity

/-!
# The canonical morphism to `Proj Γ_*(X, L)` on the functions over a standard open

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module, `S = Γ_*(X, L)` the graded section ring
of Stacks Tag 01CV and `f : X ⟶ Proj S` the canonical morphism of Stacks Tag 01PZ. For `a` a global
section of `L ^⊗ d` with `d > 0` the preimage of the standard open `D₊(a)` is the nonvanishing open
`X_a` (`Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen`), so `f` induces a
ring map `Γ(Proj S, D₊(a)) ⟶ Γ(X, X_a)`.

This file computes that map. Through the identification `S₍a₎ = Γ(Proj S, D₊(a))` of Stacks Tag
01M6 it is the chart ring map `Stacks.SectionRingChartMap.chartRingMap` of Stacks Tag 01PW, out of
which `f` itself is built; this is
`Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple`, the identification of `f` with the
chart as a morphism of schemes, read on sections. It fixes the scalar multiplication on `f_* ℱ`
over `D₊(a)`, and so upgrades the additive map
`Stacks.SectionRingProjQuasicoherent.standardOpenComparison` to a morphism of
`Γ(D₊(a), 𝒪_{Proj S})`-modules, the shape of the field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app`.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.standardOpenModuleComparison`: Stacks Tag 0B5I's local
  comparison on `D₊(a)` as a morphism of modules over the sections of the structure sheaf there,
  from the sections of `M̃` to the sections of `f_* ℱ`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.awayToSection_comp_toSpecΓ_SpecMap_awayι_appLE`: for an
  arbitrary graded ring, the morphism `V ⟶ Proj 𝒜` attached to a ring map
  `ρ : 𝒜₍r₎ ⟶ Γ(X, V)` by `Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_symm_val`
  acts on the functions over `D₊(r)` by `ρ`.
* `Stacks.SectionRingProjQuasicoherent.awayToSection_comp_projHomOfIsAmple_appLE` and
  `awayToSection_comp_projHomOfIsAmple_app`: the canonical morphism of Stacks Tag 01PZ acts on
  the functions over `D₊(a)` by the chart ring map of Stacks Tag 01PW, in the `appLE` form and
  with the inequality of opens cleared away.
* `Stacks.SectionRingProjQuasicoherent.degreeZeroHom_standardOpenEquiv_smul`: over a bare graded
  ring, semilinearity transported across Tag 01M6's standard-open identification.
* `Stacks.SectionRingProjQuasicoherent.standardOpenComparison_smul`: Tag 0B5I's local comparison
  is semilinear over the chart ring map.

## Implementation notes

The general statement is the analogue, for a chart written as
`V.toSpecΓ ≫ Spec.map ρ ≫ awayι`, of
`Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE` for the cone projection. It
uses `Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE`, which inverts
`AlgebraicGeometry.Proj.awayToSection` on Mathlib's chart `Spec 𝒜₍r₎ ⟶ Proj 𝒜`, together with
`ι_appLE_top`, `appLE_top_top` and the transport `appLE_congr_hom` along an equality of morphisms.
Passing to `f` is the factorization `Stacks.SectionRingChartOpen.chartHomOn_val` of the chart
through `Spec` of the chart ring map, with the inclusion of `X_a` post-composed; that inclusion is
an isomorphism on sections (`ι_appLE_top`), so it cancels.

`degreeZeroHom_standardOpenEquiv_smul` is stated for a bare graded ring and graded module, with no
sheaf on a scheme in the motive: at the graded module of twisted sections, a `rw` chain in a goal
whose types mention `Stacks.SectionRingProjQuasicoherent.tildeFunctor` exhausts the heartbeat
limit at `isDefEq`. For the same reason `standardOpenModuleComparison` supplies the four module
instances of `ModuleCat.ofHom` explicitly, as `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`
does: instance search does not find the module structure on the sections of `M̃` over `D₊(a)`,
whose `ModuleCat` object is a value of `AlgebraicGeometry.ProjectiveSpectrum.Proj.modulePresheaf`.

`standardOpenModuleComparison` is not Stacks Tag 0B5I's morphism `M̃ ⟶ f_* ℱ`: it is the local
datum on one standard open, indexed by a section `a` of `L ^⊗ d` with `0 < d` rather than by
`Stacks.AlgebraicGeometry.ProjTwistComparison.PositiveElem`, and the compatibility with
restriction (the field `app_restrict`) is not proved here.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Opposite
open Stacks.Ample
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (grading nvOpen)
open Stacks.AlgebraicGeometry.ProjChartSections
  (awayι_preimage_basicOpen_self awayToSection_comp_awayι_appLE ι_appLE_top appLE_top_top
    appLE_congr_hom)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple projHomOfIsAmple_preimage_projBasicOpen)
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.SectionRingProjQuasicoherent

section Chart

variable {Y : Scheme.{u}} {σ : Type u} {R : Type u} [CommRing R] [SetLike σ R]
  [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {r : R} {d : ℕ}

/-- The chart attached to a ring map out of `𝒜₍r₎` lands in `D₊(r)`. -/
theorem toSpecΓ_SpecMap_awayι_preimage (hr : r ∈ 𝒜 d) (hd : 0 < d) (V : Y.Opens)
    (ρ : CommRingCat.of (Away 𝒜 r) ⟶ Γ(Y, V)) :
    (V.toSpecΓ ≫ Spec.map ρ ≫ Proj.awayι 𝒜 r hr hd) ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤ := by
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    awayι_preimage_basicOpen_self 𝒜 hr hd, Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]

/-- **The chart attached to a ring map `ρ` out of `𝒜₍r₎` acts on the functions over `D₊(r)` by
`ρ`.** Through the identification `𝒜₍r₎ = Γ(Proj 𝒜, D₊(r))` of Stacks Tag 01M6, the morphism
`V ⟶ Proj 𝒜` that `Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_symm_val` writes as
`V.toSpecΓ ≫ Spec.map ρ ≫ awayι 𝒜 r` pulls a function on `D₊(r)` back to its value under `ρ`. -/
theorem awayToSection_comp_toSpecΓ_SpecMap_awayι_appLE (hr : r ∈ 𝒜 d) (hd : 0 < d) (V : Y.Opens)
    (ρ : CommRingCat.of (Away 𝒜 r) ⟶ Γ(Y, V)) :
    Proj.awayToSection 𝒜 r ≫
        (V.toSpecΓ ≫ Spec.map ρ ≫ Proj.awayι 𝒜 r hr hd).appLE (Proj.basicOpen 𝒜 r) ⊤
          (toSpecΓ_SpecMap_awayι_preimage 𝒜 hr hd V ρ).ge =
      ρ ≫ V.topIso.inv := by
  have hassoc : V.toSpecΓ ≫ Spec.map ρ ≫ Proj.awayι 𝒜 r hr hd =
      (V.toSpecΓ ≫ Spec.map ρ) ≫ Proj.awayι 𝒜 r hr hd := (Category.assoc _ _ _).symm
  have hpre : ((V.toSpecΓ ≫ Spec.map ρ) ≫ Proj.awayι 𝒜 r hr hd) ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤ := by
    rw [← hassoc]
    exact toSpecΓ_SpecMap_awayι_preimage 𝒜 hr hd V ρ
  have hsplit : (Proj.awayι 𝒜 r hr hd).appLE (Proj.basicOpen 𝒜 r) ⊤
        (awayι_preimage_basicOpen_self 𝒜 hr hd).ge ≫
      (V.toSpecΓ ≫ Spec.map ρ).appLE ⊤ ⊤
        (Scheme.Hom.preimage_top (V.toSpecΓ ≫ Spec.map ρ)).ge =
      ((V.toSpecΓ ≫ Spec.map ρ) ≫ Proj.awayι 𝒜 r hr hd).appLE (Proj.basicOpen 𝒜 r) ⊤ hpre.ge :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have htop : (V.toSpecΓ ≫ Spec.map ρ).appLE ⊤ ⊤
      (Scheme.Hom.preimage_top (V.toSpecΓ ≫ Spec.map ρ)).ge =
      (V.toSpecΓ ≫ Spec.map ρ).appTop :=
    appLE_top_top _ _
  rw [appLE_congr_hom hassoc (Proj.basicOpen 𝒜 r) ⊤
      (toSpecΓ_SpecMap_awayι_preimage 𝒜 hr hd V ρ).ge hpre.ge, ← hsplit, ← Category.assoc,
    awayToSection_comp_awayι_appLE 𝒜 hr hd, htop, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]

end Chart

section ProjHom

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

/-- **The canonical morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ acts on the functions over
the standard open `D₊(a)` by the chart ring map of Stacks Tag 01PW.** Read through the
identification `Γ_*(X, L)₍a₎ = Γ(Proj Γ_*(X, L), D₊(a))` of Stacks Tag 01M6 and the identification
`f ⁻¹ᵁ D₊(a) = X_a` of clause (1) of Stacks Tag 01PZ, the pullback of functions along `f` is
`Stacks.SectionRingChartMap.chartRingMap L a`.

This is `Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple` read on sections. -/
theorem awayToSection_comp_projHomOfIsAmple_appLE {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) ≫
        (projHomOfIsAmple L hL).appLE
          (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) (nvOpen L a)
          (projHomOfIsAmple_preimage_projBasicOpen L hL a hd).ge =
      CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a))) := by
  have hchart : (nvOpen L a).ι ≫ projHomOfIsAmple L hL =
      (nvOpen L a).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
            (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a)))) ≫
          Proj.awayι (grading L) (DirectSum.of (powSections L) d a)
            (Stacks.ExternalGrading.of_mem_summand d a) hd := by
    rw [Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple L hL a hd,
      ← Stacks.SectionRingChartOpen.chartHomOn_self L a hd,
      Stacks.SectionRingChartOpen.chartHomOn_val L a hd (le_refl (nvOpen L a))]
  have key : Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) ≫
        ((projHomOfIsAmple L hL).appLE
            (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) (nvOpen L a)
            (projHomOfIsAmple_preimage_projBasicOpen L hL a hd).ge ≫
          (nvOpen L a).ι.appLE (nvOpen L a) ⊤ (by simp)) =
      CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a))) ≫
        (Scheme.Opens.topIso (nvOpen L a)).inv := by
    rw [Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom hchart (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) ⊤
        _ (toSpecΓ_SpecMap_awayι_preimage (grading L)
          (Stacks.ExternalGrading.of_mem_summand d a) hd (nvOpen L a) _).ge,
      awayToSection_comp_toSpecΓ_SpecMap_awayι_appLE]
  rw [ι_appLE_top (nvOpen L a)] at key
  exact (cancel_mono (Scheme.Opens.topIso (nvOpen L a)).inv).mp
    ((Category.assoc _ _ _).trans key)

/-- Transporting the functions over `X_a` back along `f ⁻¹ᵁ D₊(a) = X_a` undoes the inequality of
opens that `AlgebraicGeometry.Scheme.Hom.appLE` carries. -/
theorem projHomOfIsAmple_app_eq {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    (projHomOfIsAmple L hL).appLE
          (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) (nvOpen L a)
          (projHomOfIsAmple_preimage_projBasicOpen L hL a hd).ge ≫
        X.presheaf.map
          (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op =
      (projHomOfIsAmple L hL).app
        (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) := by
  rw [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp,
    show ((homOfLE (projHomOfIsAmple_preimage_projBasicOpen L hL a hd).ge).op ≫
        (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op) =
      CategoryStruct.id _ from Subsingleton.elim _ _]
  simp

/-- **The ring map `f` induces on the sections over `D₊(a)` is the chart ring map of Stacks Tag
01PW**, read through `AlgebraicGeometry.Proj.awayToSection` and transported along
`f ⁻¹ᵁ D₊(a) = X_a`. This is `awayToSection_comp_projHomOfIsAmple_appLE` with the inequality of
opens cleared away. -/
theorem awayToSection_comp_projHomOfIsAmple_app {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) ≫
        (projHomOfIsAmple L hL).app
          (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) =
      CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a))) ≫
        X.presheaf.map (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op := by
  rw [← projHomOfIsAmple_app_eq L hL a hd, ← Category.assoc,
    awayToSection_comp_projHomOfIsAmple_appLE L hL a hd]

end ProjHom

section AbstractSmul

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N]
  {K : Type u} [CommRing K] [Module K N]
  (𝒮 : ℕ → AddSubgroup S) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

attribute [local instance] ProjectiveSpectrum.isPrime

/-- **Semilinearity transported across Tag 01M6's standard-open identification.** Over a bare
graded ring, an additive map out of the degree-zero localization `M₍f₎` that is semilinear over a
ring map `φ` becomes, after Tag 01M6's identification of `M₍f₎` with the sections of `M̃` over
`D₊(f)`, semilinear over `φ` for the action of the degree-zero localization on those sections. -/
theorem degreeZeroHom_standardOpenEquiv_smul {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (D : GradedModuleDegreeZeroLocalization 𝒮 𝒨 f →+ N)
    (φ : HomogeneousLocalization.Away 𝒮 f →+* K)
    (hD : ∀ (w : HomogeneousLocalization.Away 𝒮 f)
      (y : GradedModuleDegreeZeroLocalization 𝒮 𝒨 f),
      D (w • y) = φ w • D y)
    (w : HomogeneousLocalization.Away 𝒮 f)
    (z : (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    D (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
        𝒮 𝒨 hf hd (w • z)) =
      φ w • D (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
        𝒮 𝒨 hf hd z) :=
  (congrArg D
    (map_smul
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
        𝒮 𝒨 hf hd) w z)).trans (hD w _)

end AbstractSmul

section LocalDatum

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

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

/-- **Stacks Tag 0B5I's local comparison on `D₊(a)` is semilinear over the chart ring map of
Stacks Tag 01PW.** The scalars are the degree-zero localization `Γ_*(X, L)₍a₎`, which acts on the
sections of `M̃` over `D₊(a)` by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenModule` and on the
sections of `ℱ` over `X_a` through `Stacks.SectionRingChartMap.chartRingMap`. -/
theorem standardOpenComparison_smul (F : X.Modules) {d : ℕ}
    (a : Stacks.GradedSections.powSections L d) (hd : 0 < d)
    (w : HomogeneousLocalization.Away (grading L)
      (Stacks.TwistedSections.homogeneousSectionOfDegree a))
    (z : (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf (grading L)
        (Stacks.TwistedSections.moduleGrading F L)).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L)
        (Stacks.TwistedSections.homogeneousSectionOfDegree a)))) :
    standardOpenComparison L F a hd (w • z) =
      Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a)) w •
        standardOpenComparison L F a hd z :=
  degreeZeroHom_standardOpenEquiv_smul (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d a) hd
    (Stacks.TwistedSections.localizationLiftSections F L a (nvOpen L a) le_rfl)
    (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a)))
    (Stacks.TwistedSections.localizationLiftSections_smul F L a (nvOpen L a) le_rfl) w z

/-- **Stacks Tag 0B5I's local comparison on `D₊(a)`, as a morphism of modules over the sections
of `𝒪_{Proj Γ_*(X, L)}` there** — the shape the field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app` asks for, for the sheaf
associated to `Γ_*(X, L, ℱ)` and the target `f_* ℱ`.

The underlying additive map is
`Stacks.SectionRingProjQuasicoherent.standardOpenComparison`, transported along
`f ⁻¹ᵁ D₊(a) = X_a`. The content is the linearity. On the source the action of `Γ(D₊(a), 𝒪)` is
the action of the degree-zero localization through `AlgebraicGeometry.Proj.awayToSection`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.standardOpenModule_smul`), on which the comparison is
semilinear by `standardOpenComparison_smul`; on the target it is the action of `Γ(D₊(a), 𝒪)`
restricted along the ring map `f` induces there, and
`awayToSection_comp_projHomOfIsAmple_app` identifies that with the chart ring map. -/
def standardOpenModuleComparison (F : X.Modules) {d : ℕ}
    (a : Stacks.GradedSections.powSections L d) (hd : 0 < d) :
    ((tildeFunctor L).obj F).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading L)
          (Stacks.TwistedSections.homogeneousSectionOfDegree a))) ⟶
      ((Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading L)
          (Stacks.TwistedSections.homogeneousSectionOfDegree a))) :=
  @ModuleCat.ofHom _ _ _ _
    (((tildeFunctor L).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L)
        (Stacks.TwistedSections.homogeneousSectionOfDegree a)))).isAddCommGroup
    (((tildeFunctor L).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L)
        (Stacks.TwistedSections.homogeneousSectionOfDegree a)))).isModule
    (((Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L)
        (Stacks.TwistedSections.homogeneousSectionOfDegree a)))).isAddCommGroup
    (((Scheme.Modules.pushforward (projHomOfIsAmple L hL)).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L)
        (Stacks.TwistedSections.homogeneousSectionOfDegree a)))).isModule
    { toFun := fun z =>
        F.val.map (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op
          (standardOpenComparison L F a hd z)
      map_add' := fun z z' =>
        (congrArg
            (F.val.map (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op)
            (map_add (standardOpenComparison L F a hd) z z')).trans
          (map_add _ _ _)
      map_smul' := fun r z => by
        have hmem : Stacks.TwistedSections.homogeneousSectionOfDegree a ∈ grading L d :=
          Stacks.ExternalGrading.of_mem_summand d a
        have hiso : IsIso (Proj.awayToSection (grading L)
            (Stacks.TwistedSections.homogeneousSectionOfDegree a)) := by
          rw [← Proj.basicOpenIsoAway_hom (grading L)
            (Stacks.TwistedSections.homogeneousSectionOfDegree a) hmem hd]
          infer_instance
        obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso
          (Proj.awayToSection (grading L)
            (Stacks.TwistedSections.homogeneousSectionOfDegree a))).2 r
        refine Eq.trans (congrArg
          (F.val.map (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op)
          (standardOpenComparison_smul L F a hd w z)) ?_
        refine Eq.trans (PresheafOfModules.map_smul F.val _ _ _) ?_
        exact congrArg
          (· • F.val.map (eqToHom (projHomOfIsAmple_preimage_projBasicOpen L hL a hd)).op
            (standardOpenComparison L F a hd z))
          (ConcreteCategory.congr_hom
            (awayToSection_comp_projHomOfIsAmple_app L hL a hd).symm w) }

end LocalDatum

end Stacks.SectionRingProjQuasicoherent

end
