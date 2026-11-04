module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.NestedSectionBridge
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.LocalizationFunctoriality

/-!
# Stacks Tag 0B5I's local comparison on a standard open, and its naturality in `ℱ`

In the situation of Stacks Tag 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` and `f : X ⟶ Proj S` the canonical morphism of Stacks Tag 01PZ — Stacks Tag 0B5I
asks for a morphism `M̃ ⟶ f_* ℱ` on `Proj S`, functorial in `ℱ`, where `M = Γ_*(X, L, ℱ)`. The
morphism is glued from maps on the sections over the standard opens `D₊(a)` of positive-degree
homogeneous elements
(`Stacks.AlgebraicGeometry.ProjTwistComparison.homOfStandardOpenHomData`), and on `D₊(a)` the map
is Stacks Tag 0B5L's division `Γ_*(X, L, ℱ)_{(a)} ⟶ Γ(X_a, ℱ)`.

**This file assembles that local map and proves it is natural in `ℱ`.** Both halves of the
assembly are already in the tree and are only put together here: Tag 01M6 part (3) identifies the
sections of `M̃` over `D₊(a)` with the degree-zero localization `M_{(a)}`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`), and Tag
0B5L's map out of that localization is `Stacks.TwistedSections.localizationLiftSections`. The
naturality statement is the square

```
        Γ(D₊(a), M̃)  ──────────▶   Γ(X_a, ℱ)
             │                           │
    Γ(D₊(a), (Γ_*(X,L,φ))~)          Γ(X_a, φ)
             ▼                           ▼
        Γ(D₊(a), Ñ)  ──────────▶   Γ(X_a, 𝒢)
```

for `φ : ℱ ⟶ 𝒢`, `N = Γ_*(X, L, 𝒢)`, whose left vertical map is `(tildeFunctor L).map φ` read on
the sections over `D₊(a)`.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.standardOpenComparison`: **Stacks Tag 0B5I's local
  comparison on the standard open `D₊(a)`**, as a map from the sections of `M̃` there to the
  sections of `ℱ` over `X_a`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.standardOpenComparison_naturality`: **the local
  comparison is natural in `ℱ`.**
* `Stacks.SectionRingProjQuasicoherent.tildeFunctor_map_app_standardOpen`: the left vertical map
  of the square, read through the standard-open identification, is the covariance
  `Stacks.SheafOfModules.degreeZeroLocalizationMap` of the degree-zero localization in the graded
  module. This is the link to `M̃` that
  `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/LocalizationFunctoriality.lean` records as
  missing; with it, that file's naturality square becomes a square about the sections of `M̃`.
* `Stacks.SectionRingProjQuasicoherent.localizationLiftSections_mapDegreeZeroLocalization`:
  **Stacks Tag 0B5L's map is natural in `ℱ` at the level of sections.** Naturality was available
  for the map into the degree-zero twisted sections on the slice site over `V`
  (`Stacks.TwistedSections.localizationLiftOfMonoidal_mapDegreeZeroLocalization`); reading the
  quotient as a section of `ℱ` over `V` keeps it, because the slice-unit bridge is natural.
* `Stacks.SectionRingProjQuasicoherent.schemeOpenUnitHomAddEquiv_twistSectionsMap`: that bridge's
  naturality — carrying a morphism out of the monoidal unit along the restriction of `φ` and
  reading the result as a section is `φ` on sections.

## Implementation notes

**No `stacks` attribute.** Tag 0B5I's assertion is about the glued morphism `M̃ ⟶ f_* ℱ` and its
functoriality; what is proved here is the local datum the gluing consumes, and the registration of
the tag belongs with the glued morphism. Attaching the tag to a local statement would report the
tag as covered when the gluing is not available; see `## What is not done` and the module
documentation of
`StacksFrontier/AlgebraicGeometry/SectionRingProjQuasicoherent/Comparison.lean`.

**Why the link to `M̃` is factored through an abstract lemma.**
`Stacks.SectionRingProjQuasicoherent.associatedModuleSheafMap_standardOpenEquiv` is stated for a
bare graded ring and two bare graded modules, with no scheme in sight, and
`tildeFunctor_map_app_standardOpen` is its instance at the graded module of twisted sections. The
instance is what is wanted, but it cannot be proved in place: rewriting with
`Stacks.SheafOfModules.degreeZeroLocalizationMap_coe` inside a goal whose types mention
`tildeFunctor` exhausts the heartbeat limit at `isDefEq`, while the abstract statement
elaborates in seconds. For the same reason
`standardOpenComparison_naturality` is a chain of `Eq.trans` and not a `rw`.

**The two gradings of the section ring are one.** The abstract lemma is instantiated at
`Stacks.AmpleFiniteAvoidance.grading`, the family `Proj Γ_*(X, L)` is formed from, while the
twisted-section development states its localizations over
`Stacks.TwistedSections.sectionGrading`; the two are equal by `rfl`
(`Stacks.TwistedSections.sectionGrading_eq_ampleGrading`), so no transport appears.

## What is not done

**This does not produce Stacks Tag 0B5I's morphism `M̃ ⟶ f_* ℱ`**, and therefore not Tag 01QJ's
family `c` either. Of the two inputs of
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData`, one is now available and one
is not; neither is naturality.

* **The field `app` is a morphism of modules over `Γ(D₊(a), 𝒪_{Proj S})`, and the map built here
  is only additive. This is now done, in the sibling
  `StacksFrontier/AlgebraicGeometry/SectionRingProjQuasicoherent/ChartSections.lean`, and the record
  below of what it was blocked on is withdrawn.** Its semilinearity over the chart ring map of
  Stacks Tag 01PW is `Stacks.TwistedSections.localizationLiftSections_smul`, so what was owed was
  the identification of that chart ring map with the action of `𝒪_{Proj S}` on `f_* ℱ`, that is
  with the ring map `(projHomOfIsAmple L hL)` induces on the sections over `D₊(a)`. The record
  said that the tree identifies the canonical morphism with the chart only as a *morphism of
  schemes* — on `X_a` it is `Stacks.SectionRingChartMap.chartHom` by
  `Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple`, with
  `Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen` for the preimage — and
  nowhere as a map on sections over `D₊(a)`. That map on sections is
  `Stacks.SectionRingProjQuasicoherent.awayToSection_comp_projHomOfIsAmple_appLE`, proved from
  `Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE` exactly as
  `Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE` is for the cone projection,
  and the resulting morphism of modules is
  `Stacks.SectionRingProjQuasicoherent.standardOpenModuleComparison`.
* **The field `app_restrict` compares the local maps at two different homogeneous elements, and
  is the only field still missing. Its division side is now done, and the record below of what
  blocked it is withdrawn.** The two halves are
  `Stacks.TwistedSections.openDivision_restrict` — the shrink at a fixed generator, with both
  maps on the slice site over the open they live on
  (`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestrictionShrink.lean`) — and
  `Stacks.TwistedSections.openDivision_gsmul_changeGenerator` — the change of generator over a
  common open, for a relation `y · a = bᴺ` in the section ring
  (`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionGeneratorChange.lean`). The record said that the divisions
  at two sections are related by nothing and that the shrink is available only on the *iterated*
  slice site over `(X_a, X_b)`, whereas the local map at `b` lives on the slice site over `X_b`,
  with nothing identifying the two restrictions as monoidal functors. The second half of that is
  still true of `Stacks.TwistedSections.localizationLiftNestedSections_apply`; what is withdrawn
  is the conclusion that the identification is needed. Multiplication by `aⁿ` is a *morphism*
  `ℱ ⟶ ℱ ⊙ (d n)` of `𝒪_X`-modules (`Stacks.TwistedSections.twistMul`), the division over an
  open is its inverse on the sections there
  (`Stacks.TwistedSections.twistMul_app_openDivision`), and a morphism commutes with every
  restriction map by naturality — so the shrink is proved without comparing two sites.

  What `app_restrict` still owes is the **source** side. The restriction
  `M̃(D₊(a)) ⟶ M̃(D₊(b))` is Stacks Tag 01M4's degree-zero restriction map by
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.standardOpenEquiv_restrict`, and what is missing is
  its value on a fraction `t / aⁿ` — the module analogue of
  `Stacks.SectionRingChartOpen.chartRingMap_comp_awayMap`, for which
  `ProjectiveSpectrum.GradedModuleRestrictionMaps` offers only `map_mk`, the value on a fraction
  with denominator `1`. The relation `bᴺ = y · a` that `openDivision_gsmul_changeGenerator`
  consumes is available: it is
  `AlgebraicGeometry.ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le`.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite DirectSum MonoidalCategory
open Stacks.Ample Stacks.GradedSections
open Stacks.AmpleFiniteAvoidance (grading nvOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionProduct (globalSection)
open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOpenUnitHomAddEquiv)
open Stacks.TwistedSections (twistSections twistSectionsMap homogeneousSectionOfDegree moduleGrading
  sectionGrading sectionAtNonvanishingOpenOfDegree localizationLiftSections localizationLiftOverOpen
  twistModuleLinearMap twistModuleHom_mem_moduleGrading)

universe u

namespace Stacks.SectionRingProjQuasicoherent

section Abstract

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  (𝒮 : ℕ → AddSubgroup S) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
  (𝒩 : ℤ → AddSubgroup N) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]

attribute [local instance] ProjectiveSpectrum.isPrime

/-- **On a positive-degree standard open, the morphism of associated sheaves induced by a
degree-preserving map is the covariance of the degree-zero localization.** This is
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen`, whose
conclusion is an equation between the underlying fractions, read back inside the degree-zero
localization: both sides are `LocalizedModule.map` of the graded map, the right-hand one by
`Stacks.SheafOfModules.degreeZeroLocalizationMap_coe`. -/
theorem associatedModuleSheafMap_standardOpenEquiv (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd
        (ConcreteCategory.hom
          ((Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
            𝒮 𝒨 𝒩 φ hφ).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))) z)
      = Stacks.SheafOfModules.degreeZeroLocalizationMap 𝒮 𝒨 𝒩 φ hφ f
          (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd z) :=
  Subtype.ext
    ((Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen
        𝒮 𝒨 𝒩 φ hφ hf hd z).trans
      (Stacks.SheafOfModules.degreeZeroLocalizationMap_coe 𝒮 𝒨 𝒩 φ hφ f _).symm)

end Abstract

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### Naturality of Stacks Tag 0B5L's map in the module -/

omit [IsInvertibleModule X L] in
/-- **The slice-unit bridge is natural in the module.** A degree-zero twisted section over `V` is
a morphism out of the monoidal unit of the modules on the slice site over `V`; carrying it along
the restriction of `φ : ℱ ⟶ 𝒢` and reading the result as a section of `𝒢` over `V` is `φ` on
sections. Both sides are the value at `1` of a composite of morphisms of presheaves of modules, so
this is `Stacks.SectionRingGeometric.tensorUnitHomAddEquiv_comp` at the slice site. -/
theorem schemeOpenUnitHomAddEquiv_twistSectionsMap (V : X.Opens) {F G : X.Modules} (φ : F ⟶ G)
    (t : twistSections ((schemeOpenRestriction X V).obj F)
      ((schemeOpenRestriction X V).obj L) 0) :
    schemeOpenUnitHomAddEquiv V G (twistSectionsMap ((schemeOpenRestriction X V).map φ) 0 t)
      = ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) (schemeOpenUnitHomAddEquiv V F t) :=
  Stacks.SectionRingGeometric.tensorUnitHomAddEquiv_comp _ _ Over.mkIdTerminal t
    ((schemeOpenRestriction X V).map φ)

/-- **Stacks Tag 0B5L's comparison map is natural in `ℱ`, at the level of sections.** Pushing a
degree-zero fraction of `Γ_*(X, L, ℱ)` forward along `φ : ℱ ⟶ 𝒢` and then dividing by the power of
`a` over `V` is dividing first and then applying `φ` on sections over `V`.

Naturality is `Stacks.TwistedSections.localizationLiftOfMonoidal_mapDegreeZeroLocalization` for
the map into the degree-zero twisted sections on the slice site over `V`; reading the quotient as
a section of `ℱ` over `V` preserves it by `schemeOpenUnitHomAddEquiv_twistSectionsMap`. -/
theorem localizationLiftSections_mapDegreeZeroLocalization {F G : X.Modules} (φ : F ⟶ G)
    {d : ℕ} (a : powSections L d) (V : X.Opens) (hV : V ≤ nvOpen L a)
    (z : sectionAtNonvanishingOpenOfDegree F L a) :
    localizationLiftSections G L a V hV
        (Stacks.SheafOfModules.degreeZeroLocalizationMap (sectionGrading L)
          (moduleGrading F L) (moduleGrading G L) (twistModuleLinearMap φ)
          (twistModuleHom_mem_moduleGrading φ) (homogeneousSectionOfDegree a) z)
      = ConcreteCategory.hom (Scheme.Modules.Hom.app φ V)
          (localizationLiftSections F L a V hV z) := by
  have := Stacks.TwistedSections.isIso_mapPowSections_openRestriction L a hV
  have hlift : localizationLiftOverOpen G L a V hV
      (Stacks.SheafOfModules.degreeZeroLocalizationMap (sectionGrading L)
        (moduleGrading F L) (moduleGrading G L) (twistModuleLinearMap φ)
        (twistModuleHom_mem_moduleGrading φ) (homogeneousSectionOfDegree a) z)
      = twistSectionsMap ((schemeOpenRestriction X V).map φ) 0
          (localizationLiftOverOpen F L a V hV z) :=
    Stacks.TwistedSections.localizationLiftOfMonoidal_mapDegreeZeroLocalization
      (schemeOpenRestriction X V) a φ z
  show schemeOpenUnitHomAddEquiv V G (localizationLiftOverOpen G L a V hV _) = _
  rw [hlift, schemeOpenUnitHomAddEquiv_twistSectionsMap]
  rfl

/-! ### Stacks Tag 0B5I's local comparison on a standard open -/

/-- **The link to `M̃`.** The morphism `(Γ_*(X, L, φ))~` induced by `φ : ℱ ⟶ 𝒢` on the sheaves
associated to the graded modules of twisted sections is, on the sections over `D₊(a)` and through
Tag 01M6's standard-open identification, the covariance
`Stacks.SheafOfModules.degreeZeroLocalizationMap` of the degree-zero localization. -/
theorem tildeFunctor_map_app_standardOpen {F G : X.Modules} (φ : F ⟶ G) {d : ℕ}
    (a : powSections L d) (hd : 0 < d)
    (z : ((tildeFunctor L).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a)))) :
    AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
        (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand d a) hd
        (ConcreteCategory.hom (((tildeFunctor L).map φ).val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a)))) z)
      = Stacks.SheafOfModules.degreeZeroLocalizationMap (grading L)
          (moduleGrading F L) (moduleGrading G L) (twistModuleLinearMap φ)
          (twistModuleHom_mem_moduleGrading φ) (homogeneousSectionOfDegree a)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
            (grading L) (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) hd z) :=
  associatedModuleSheafMap_standardOpenEquiv (grading L) (moduleGrading F L) (moduleGrading G L)
    (twistModuleLinearMap φ) (twistModuleHom_mem_moduleGrading φ)
    (Stacks.ExternalGrading.of_mem_summand d a) hd z

/-- **Stacks Tag 0B5I's local comparison on the standard open `D₊(a)`**: the sections of
`M̃ = (Γ_*(X, L, ℱ))~` over `D₊(a)` are the degree-zero localization `Γ_*(X, L, ℱ)_{(a)}` by Tag
01M6 part (3), and Stacks Tag 0B5L's division carries that to the sections of `ℱ` over `X_a`,
which is the preimage of `D₊(a)` under the canonical morphism of Stacks Tag 01PZ. -/
def standardOpenComparison (F : X.Modules) {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    ((tildeFunctor L).obj F).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a))) →+
      Γ(F, nvOpen L a) :=
  (localizationLiftSections F L a (nvOpen L a) le_rfl).comp
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) hd).toAddEquiv.toAddMonoidHom

/-- The local comparison is Tag 0B5L's division after Tag 01M6's identification. -/
theorem standardOpenComparison_apply (F : X.Modules) {d : ℕ} (a : powSections L d) (hd : 0 < d)
    (z : ((tildeFunctor L).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a)))) :
    standardOpenComparison L F a hd z
      = localizationLiftSections F L a (nvOpen L a) le_rfl
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
            (grading L) (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) hd z) :=
  rfl

/-- **Stacks Tag 0B5I's local comparison is natural in `ℱ`.** For `φ : ℱ ⟶ 𝒢`, the square formed
by the local comparisons at `D₊(a)`, the morphism `(Γ_*(X, L, φ))~` on the sections of the
associated sheaves, and `φ` on the sections over `X_a`, commutes.

This is the local half of the functoriality Stacks Tag 0B5I asserts, and hence of clause (b) of
Stacks Tag 01QJ. The glued morphism `M̃ ⟶ f_* ℱ` it is the local datum of is not available; see
`## What is not done` in the module documentation. -/
theorem standardOpenComparison_naturality {F G : X.Modules} (φ : F ⟶ G) {d : ℕ}
    (a : powSections L d) (hd : 0 < d)
    (z : ((tildeFunctor L).obj F).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a)))) :
    standardOpenComparison L G a hd
        (ConcreteCategory.hom (((tildeFunctor L).map φ).val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (homogeneousSectionOfDegree a)))) z)
      = ConcreteCategory.hom (Scheme.Modules.Hom.app φ (nvOpen L a))
          (standardOpenComparison L F a hd z) :=
  (standardOpenComparison_apply L G a hd _).trans
    ((congrArg (localizationLiftSections G L a (nvOpen L a) le_rfl)
          (tildeFunctor_map_app_standardOpen L φ a hd z)).trans
      ((localizationLiftSections_mapDegreeZeroLocalization L φ a (nvOpen L a) le_rfl _).trans
        (congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app φ (nvOpen L a)))
          (standardOpenComparison_apply L F a hd z).symm)))

end Stacks.SectionRingProjQuasicoherent

end
