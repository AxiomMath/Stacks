module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplaySurjectivity
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.ModulesOverOpenSliceHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSupportUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOfOpenThetaTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescentSingleChart

/-!
# Stacks 01YB on a chart of an algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals, let `U = X ∖ V(ℐ)` be its open complement, let `𝒢` be a coherent and `ℱ` a
quasi-coherent `𝒪_X`-module, and let `θ : 𝒢|_U ⟶ ℱ|_U`.  This file carries `θ` to an étale
scheme chart `A` of `X`, applies the first display of [Stacks, Tag 01YB] on the chart's scheme,
and carries the resulting morphism back to the slice of the small étale site of `X` at the chart.
That is the first half of the surjectivity argument for [Stacks, Tag 07UM]; the second half, the
descent from the chart, is **not** proved here — see the implementation notes.

The chart restriction of an `𝒪_X`-module is used throughout in the direct-image spelling
`AlgebraicGeometry.Space.chartPush` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleDirectImage.lean`, where its sections, its
restriction maps and its action on morphisms are each one layer deep.  The chosen spelling
`AlgebraicGeometry.Space.chartSchemeModule` is related to it by the isomorphism
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` and is used only where coherence,
quasi-coherence or the Hom-set transport of
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` is invoked.

## Main definitions

* `AlgebraicGeometry.Space.chartPush` is the chart restriction of an `𝒪_X`-module written as the
  direct image along the composite comparison functor of the chart, and
  `AlgebraicGeometry.Space.chartPushEquiv` is its sections identification.
* `AlgebraicGeometry.Space.chartTheta` and `AlgebraicGeometry.Space.chartThetaOver` are the
  components of `θ` on the sections of the chart restrictions over the Zariski opens of the
  chart's scheme off the support, and the morphism of modules they assemble into.
* `AlgebraicGeometry.Space.chartPushFactor` is the factorization of the chart restriction of
  `ℐᵏ𝒢 ⟶ 𝒢` through `Iᵏ` times the chart restriction of `𝒢`.
* `AlgebraicGeometry.Space.chartAlpha` reads a morphism out of `Iᵏ` times the chart restriction of
  `𝒢` as a morphism of the restrictions to the slice of the small étale site of `X` at the chart.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_chartPush`,
  `AlgebraicGeometry.Space.isFiniteType_chartPush` and
  `AlgebraicGeometry.Space.isCoherent_chartPush`: the direct-image spelling of the chart
  restriction is quasi-coherent, and is coherent on a chart whose scheme is locally Noetherian.
* `AlgebraicGeometry.Space.chartThetaLinear_naturality`: the components of `θ` at the opens of the
  chart's scheme commute with restriction, which is the hypothesis
  `AlgebraicGeometry.Scheme.Modules.overHomOfSections` asks for.
* `AlgebraicGeometry.Space.chartPushι_app_mem`: **the chart restriction of `ℐᵏ𝒢` lands in `Iᵏ`
  times the chart restriction of `𝒢`.**
* `AlgebraicGeometry.Space.exists_homRestrict_eq_chartThetaOver`: **[Stacks, Tag 01YB] on the
  chart's scheme, applied to the transport of `θ`** — on a chart whose scheme is Noetherian the
  transported morphism is the restriction of a morphism out of `Iᵏ` times the chart restriction of
  `𝒢`, for some `k`.

## Implementation notes

**No `@[stacks 07UM]` attribute is placed here.**  Tag 07UM asserts that the canonical maps of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitOverComplement.lean` are bijective, and
only the chart half of surjectivity is proved here.  The attribute sits on the covering set in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitBijective.lean`.

**The descent from the chart is no longer open.**  It is
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitChartDescent.lean`, which reaches `X` by
raising the exponent of the ideal until the two relocalizations of the chart transport to the
kernel pair agree, gluing with
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod`, and identifying the result with
`θ` over the charts lying above a surjective `W` — which cover, `ℱ|_U` being separated.  That
route needs neither of the two inputs below, which are the ones the *comparison of direct
systems* would have needed; they are recorded because they remain missing from the tree and are
worth not rediscovering:

1. **`AlgebraicGeometry.Space.chartPushFactor` is only a one-way factorization.**  Its reverse,
   which would make it an isomorphism, is the inclusion `Iᵏ · (chart restriction of 𝒢) ⊆ chart
   restriction of ℐᵏ𝒢`.  Its two missing ingredients are the semilinear transport of
   `AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule` along
   `AlgebraicGeometry.Space.chartSectionsRingHom` — the converse of
   `Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top` — and the statement that a cover of
   a Zariski open of the chart's scheme by affine opens induces a covering sieve of
   `AlgebraicGeometry.Space.openChartOfComparison` of that open in the small étale site of `X`.
   Without the isomorphism the direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` cannot be compared with the
   direct system of the first display of [Stacks, Tag 01YB] on the chart's scheme, so the
   injectivity clause of that display is unusable on a chart.
2. **Nothing relates the chart transport at two charts.**  `AlgebraicGeometry.Space.chartAlpha` is
   built from `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv`, which is assembled from
   reindexing equivalences and from Descent, Proposition 03DX (2), so a morphism it produces has
   no computed component at a chart which is not a Zariski open of the chart's scheme.  The
   compatibility condition of the one-chart gluing
   `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` is a condition on the kernel
   pair `A ⨯ A`, whose charts are of exactly that kind, so closing it needs a naturality statement
   for `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` in the chart — equivalently, an étale
   base-change comparison identifying the chart restriction at `A ⨯ A` with the pullback along the
   projection of the chart restriction at `A`.  No such statement exists in the tree.

**The direct-image spelling is what makes the sections statements one layer deep.**  Every
statement below about the sections of a chart restriction, about its restriction maps and about
its action on morphisms is an instantiation of a one-layer generic lemma for
`CategoryTheory.SheafOfModules.pushforward` at
`AlgebraicGeometry.Space.chartComparisonRingMap`, which is a `def` and so is not unfolded; at the
four-layer spelling the same statements cost the heartbeat budget.  In particular
`AlgebraicGeometry.Space.chartPush_presheaf_map_apply`,
`AlgebraicGeometry.Space.chartTheta_apply` and the `hrfl` step of
`AlgebraicGeometry.Space.chartPushι_app_mem_chartSubmodule` hold by `rfl`, and the sections
identification is the `CategoryTheory.eqToIso` of an equality proved by a generic lemma rather
than a composite of comparison maps.

**Coherence is transported, not reproved.**  `AlgebraicGeometry.Space.chartSchemeModule` is a
chosen preimage, so its relation to the direct image is an isomorphism and not an equality;
coherence of the direct image is obtained from quasi-coherence and finite type through
Stacks 01XZ (2) ⇒ (1) rather than by transporting the coherence predicate: the class
`SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, which is the one
the scheme-level first display of [Stacks, Tag 01YB] asks for, is not the class
`Stacks.SheafOfModules.IsCoherent` for which the
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance is registered.  Finite type,
on the other hand, is a single predicate and *is* transported, by
`Stacks.SheafOfModules.isFiniteType_of_iso`.

**Equations are passed as arguments, never rewritten.**  The chart which a Zariski open cuts out
has two spellings, `AlgebraicGeometry.Space.openChart` and
`AlgebraicGeometry.Space.openChartOfComparison`, which are equal but not definitionally so, and
module-level statements use the second.  The transport of `θ` therefore supplies
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj` to
`AlgebraicGeometry.Space.pc_idealComplementChart` and to
`AlgebraicGeometry.Space.complementHomOnChart_naturality_of_eq` as a parameter, and
`AlgebraicGeometry.Space.hom_ext_of_toScheme_map_eq` is not needed: the lift is built at
`AlgebraicGeometry.Space.openChartOfComparisonHom`.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

universe w m v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fu : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [Fu.IsContinuous J K]
  (φ : S ⟶ (Fu.sheafPushforwardContinuous RingCat.{w} J K).obj R)

/-- The component of the direct image of a morphism of sheaves of modules. -/
theorem pushforward_map_val_app {M N : _root_.SheafOfModules.{m} R} (f : M ⟶ N) (A : C) :
    ((_root_.SheafOfModules.pushforward.{m} φ).map f).val.app (op A) =
      (ModuleCat.restrictScalars (φ.hom.app (op A)).hom).map (f.val.app (op (Fu.obj A))) := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-! ### The chart restriction, as a direct image -/

/-- The chart restriction of an `𝒪_X`-module, written as the direct image along the composite
comparison functor of the chart. -/
abbrev chartPush (A : SmallEtale B S hS X.1) :
    AlgebraicGeometry.Scheme.Modules (chartScheme A) :=
  (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M

/-- The sections of `AlgebraicGeometry.Space.chartPush` over a Zariski open of the chart's
scheme are the sections of the module over the étale chart which that open cuts out. -/
theorem chartPush_obj (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    (chartPush B S hS X M A).val.obj (op V) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
        (M.val.obj (op (openChartOfComparison B S hS X A V))) :=
  chartComparisonPushforward_obj_val_obj B S hS X M A V

/-- The sections identification of `AlgebraicGeometry.Space.chartPush`, as a linear
equivalence. -/
def chartPushEquiv (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    (chartPush B S hS X M A).val.obj (op V)
      ≃ₗ[(chartScheme A).ringCatSheaf.obj.obj (op V)]
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
          (M.val.obj (op (openChartOfComparison B S hS X A V))) :=
  (eqToIso (chartPush_obj B S hS X M A V)).toLinearEquiv

/-- The sections identification of `AlgebraicGeometry.Space.chartPush` is the identity on
underlying elements. -/
theorem chartPushEquiv_apply (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (x : (chartPush B S hS X M A).val.obj (op V)) :
    chartPushEquiv B S hS X M A V x = x := rfl

/-- The sections identification of `AlgebraicGeometry.Space.chartPush` is semilinear over
`AlgebraicGeometry.Space.chartSectionsRingHom`. -/
theorem chartPushEquiv_smul (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (r : (chartScheme A).ringCatSheaf.obj.obj (op V))
    (x : (chartPush B S hS X M A).val.obj (op V)) :
    chartPushEquiv B S hS X M A V (r • x) =
      chartSectionsRingHom B S hS X A V r •
        (show M.val.obj (op (openChartOfComparison B S hS X A V)) from
          chartPushEquiv B S hS X M A V x) :=
  (map_smul (chartPushEquiv B S hS X M A V) r x).trans
    (ModuleCat.restrictScalars.smul_def' (chartSectionsRingHom B S hS X A V) r _)

/-! ### Quasi-coherence and coherence of the direct-image spelling -/

/-- **`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` with its category pinned to
`CategoryTheory.SheafOfModules` over the structure sheaf of the chart's scheme.**  The same
isomorphism; only the spelling of the category it lives in is fixed. -/
def chartSchemeModuleIsoRestrictModuleSheaf (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (chartSchemeModule B S hS X M hM A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ≅
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X M hM A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) :=
  chartSchemeModuleIsoRestrictModule B S hS X M hM A

/-- **`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_eq_pushforward` with its
type pinned to `CategoryTheory.SheafOfModules` over the structure sheaf of the chart's scheme.**
The same equality; only the spelling of the type it is an equality in is fixed. -/
theorem restrictModule_chartSchemeEtaleModule_eq_chartPush (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X M hM A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf)
      = chartPush B S hS X M A :=
  restrictModule_chartSchemeEtaleModule_eq_pushforward B S hS X M hM A

/-- The chosen chart restriction of a quasi-coherent `𝒪_X`-module is isomorphic to its
direct-image spelling. -/
def chartSchemeModuleIsoChartPush (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    (chartSchemeModule B S hS X M hM A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ≅
      chartPush B S hS X M A :=
  chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A ≪≫
    eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)

/-- `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is the composite of its two pinned
factors.  Stated separately from
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom` because
`CategoryTheory.Iso.trans_hom` applies only when the left-hand side is *literally* a
`CategoryTheory.Iso.trans`. -/
theorem chartSchemeModuleIsoChartPush_eq (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    chartSchemeModuleIsoChartPush B S hS X M hM A =
      chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A ≪≫
        eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A) := rfl

/-- **The forward map of `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is the composite
of its two pinned factors.**  Both factors and the composite are morphisms of
`CategoryTheory.SheafOfModules` over the structure sheaf of the chart's scheme, so
`CategoryTheory.Iso.trans_hom` applies verbatim; at the unpinned spelling the composite is
elaborated in `AlgebraicGeometry.Scheme.Modules` and no generic lemma matches it. -/
theorem chartSchemeModuleIsoChartPush_hom (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (chartSchemeModuleIsoChartPush B S hS X M hM A).hom =
      (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom ≫
        (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)).hom :=
  (congrArg Iso.hom (chartSchemeModuleIsoChartPush_eq B S hS X M hM A)).trans
    (Iso.trans_hom _ _)

/-- The forward map of the pinned factor is the forward map of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` on sections, compared **unapplied**:
applied, the two spellings of the chart restriction are matched at every occurrence. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom.val.app (op V) =
      (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V) := rfl

/-- The direct-image spelling of the chart restriction of a quasi-coherent `𝒪_X`-module is
quasi-coherent. -/
theorem isQuasicoherent_chartPush (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    SheafOfModules.IsQuasicoherent (chartPush B S hS X M A) :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf)
    (chartSchemeModuleIsoChartPush B S hS X M hM A)
    (isQuasicoherent_chartSchemeModule B S hS X M hM A)

/-- The direct-image spelling of the chart restriction of a coherent `𝒪_X`-module is of finite
type on every étale scheme chart. -/
theorem isFiniteType_chartPush (hM : IsCoherent B S hS X.1 X.2 M)
    (A : SmallEtale B S hS X.1) :
    (chartPush B S hS X M A).IsFiniteType :=
  have _hft0 := isFiniteType_chartSchemeModule_of_isCoherent B S hS X M hM A
  Stacks.SheafOfModules.isFiniteType_of_iso
    (chartSchemeModuleIsoChartPush B S hS X M hM.toIsQuasicoherentOnSite A)

/-- **The direct-image spelling of the chart restriction of a coherent `𝒪_X`-module is coherent
on every chart whose scheme is locally Noetherian.**  This is
`AlgebraicGeometry.Space.isCoherent_chartSchemeModule_of_isLocallyNoetherian` at the
direct-image spelling. -/
theorem isCoherent_chartPush (hM : IsCoherent B S hS X.1 X.2 M)
    (A : SmallEtale B S hS X.1) (hV : IsLocallyNoetherian (chartScheme A)) :
    SheafOfModules.IsCoherent (chartPush B S hS X M A) :=
  have _hln : IsLocallyNoetherian (chartScheme A) := hV
  have _hqc := isQuasicoherent_chartPush B S hS X M hM.toIsQuasicoherentOnSite A
  have _hft := isFiniteType_chartPush B S hS X M hM A
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### The transport of `θ` to a chart -/

variable (I : IdealSheaves B S hS X.1 X.2)
  (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
  (G F : Modules.{u, u} B S hS X.1 X.2)
  (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
    (restrictToIdealComplement B S hS X I).obj F)

/-- The component of `θ : 𝒢|_U ⟶ ℱ|_U` on the sections of the chart restrictions over a Zariski
open of a chart's scheme lying off the support of the chartwise sheaf of ideals. -/
def chartTheta (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
      (chartScheme A).Opens)) :
    (chartPush B S hS X G A).val.obj (op V) ⟶ (chartPush B S hS X F A).val.obj (op V) :=
  (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).map
    (homOnChart B S hS X I G F θ
      ((pc_idealComplementChart B S hS X I hIc A V hV).trans
        (openChart_eq_chartLocalization_opensObj B S hS X A V).symm))

/-- The component of `θ` at a chart's open is the transported component of `θ` on the sections
over the étale chart which that open cuts out. -/
theorem chartTheta_apply (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
      (chartScheme A).Opens))
    (x : (chartPush B S hS X G A).val.obj (op V)) :
    (chartTheta B S hS X I hIc G F θ A V hV).hom x =
      (homOnChart B S hS X I G F θ
        ((pc_idealComplementChart B S hS X I hIc A V hV).trans
          (openChart_eq_chartLocalization_opensObj B S hS X A V).symm)).hom x := rfl

/-- The component of `θ` at a chart's open, as a linear map on sections. -/
def chartThetaLinear (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
      (chartScheme A).Opens)) :
    Γ(chartPush B S hS X G A, V) →ₗ[Γ(chartScheme A, V)] Γ(chartPush B S hS X F A, V) :=
  (chartTheta B S hS X I hIc G F θ A V hV).hom

/-- The restriction maps of `AlgebraicGeometry.Space.chartPush`, read on a section. -/
theorem chartPush_presheaf_map_apply (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V) (x : Γ(chartPush B S hS X M A, V)) :
    (chartPush B S hS X M A).presheaf.map (homOfLE h).op x =
      M.val.map (openChartOfComparisonHom B S hS X A h).op x := rfl

/-- **The components of `θ` at the opens of a chart's scheme commute with restriction.**  This is
the naturality hypothesis `AlgebraicGeometry.Scheme.Modules.overHomOfSections` asks for. -/
theorem chartThetaLinear_naturality (A : SmallEtale B S hS X.1)
    (V V' : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
      (chartScheme A).Opens))
    (hV'V : V' ≤ V) (g : Γ(chartPush B S hS X G A, V)) :
    (chartPush B S hS X F A).presheaf.map (homOfLE hV'V).op
        (chartThetaLinear B S hS X I hIc G F θ A V hV g) =
      chartThetaLinear B S hS X I hIc G F θ A V' (hV'V.trans hV)
        ((chartPush B S hS X G A).presheaf.map (homOfLE hV'V).op g) :=
  (chartPush_presheaf_map_apply B S hS X F A hV'V _).trans
    (complementHomOnChart_naturality_of_eq B S hS X I G F θ hIc A hV'V hV
      (openChart_eq_chartLocalization_opensObj B S hS X A V').symm
      (openChart_eq_chartLocalization_opensObj B S hS X A V).symm
      (openChartOfComparisonHom B S hS X A hV'V) g).symm

/-- **The transport of `θ : 𝒢|_U ⟶ ℱ|_U` to a chart**: the morphism of the chart restrictions
over the complement of the support of the chartwise sheaf of ideals, which is the open over
which [Stacks, Tag 01YB] is stated on the chart's scheme. -/
def chartThetaOver (A : SmallEtale B S hS X.1) :
    (chartPush B S hS X G A).over
        ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
          (chartScheme A).Opens) ⟶
      (chartPush B S hS X F A).over
        ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
          (chartScheme A).Opens) :=
  AlgebraicGeometry.Scheme.Modules.overHomOfSections _
    (fun V hV => chartThetaLinear B S hS X I hIc G F θ A V hV)
    (fun V V' hVW hV'V g =>
      chartThetaLinear_naturality B S hS X I hIc G F θ A V V' hVW hV'V g)

/-- The transport of `θ` to a chart, read on the sections over a Zariski open off the
support. -/
theorem overApp_chartThetaOver (A : SmallEtale B S hS X.1) {V : (chartScheme A).Opens}
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
      (chartScheme A).Opens))
    (g : Γ(chartPush B S hS X G A, V)) :
    Stacks.AlgebraicGeometry.IdealPowerColimit.overApp
        (chartThetaOver B S hS X I hIc G F θ A) hV g =
      (chartTheta B S hS X I hIc G F θ A V hV).hom g := rfl

/-! ### `ℐᵏ𝒢` on the chart sits inside `Iᵏ` times `𝒢` on the chart -/

/-- The chart restriction of the inclusion `ℐᵏ𝒢 ⟶ 𝒢`. -/
abbrev chartPushι (A : SmallEtale B S hS X.1) (k : ℕ) :
    chartPush B S hS X (idealPowModule I k G) A ⟶ chartPush B S hS X G A :=
  (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map
    (idealPowModuleι I k G)

/-- The restriction to an affine open of the chart's scheme of a section of the chart
restriction of `ℐᵏ𝒢`, read through the chart sections identification, is a section of `ℐᵏ𝒢`
over the étale chart which that affine open cuts out. -/
theorem chartPushι_app_mem_chartSubmodule (A : SmallEtale B S hS X.1) (k : ℕ)
    {V : (chartScheme A).Opens}
    (x : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V))
    (W : (chartScheme A).affineOpens) (hW : W.1 ≤ V) :
    (chartPushEquiv B S hS X G A W.1).toAddEquiv
        ((chartPush B S hS X G A).presheaf.map (homOfLE hW).op
          (((chartPushι B S hS X I G A k).val.app (op V)).hom x))
      ∈ chartSubmodule B S hS X.1 X.2 (idealPowSubmodule I k G)
          (openChartOfComparison B S hS X A W.1) := by
  have hnat := PresheafOfModules.naturality_apply (idealPowModuleι I k G).val
    (openChartOfComparisonHom B S hS X A hW).op x
  have hrfl : (chartPushEquiv B S hS X G A W.1).toAddEquiv
        ((chartPush B S hS X G A).presheaf.map (homOfLE hW).op
          (((chartPushι B S hS X I G A k).val.app (op V)).hom x)) =
      (G.val.map (openChartOfComparisonHom B S hS X A hW).op).hom
        (((idealPowModuleι I k G).val.app
          (op (openChartOfComparison B S hS X A V))).hom x) := rfl
  refine Eq.mpr (congrArg (fun y : G.val.obj (op (openChartOfComparison B S hS X A W.1)) =>
    y ∈ chartSubmodule B S hS X.1 X.2 (idealPowSubmodule I k G)
      (openChartOfComparison B S hS X A W.1)) (hrfl.trans hnat.symm)) ?_
  exact ((idealPowModule I k G).val.map
    (openChartOfComparisonHom B S hS X A hW).op).hom x |>.2

/-- **The chart restriction of `ℐᵏ𝒢` lands in `Iᵏ` times the chart restriction of `𝒢`.**
Membership over an arbitrary Zariski open of the chart's scheme is tested on the affine opens
inside it, and there the chart sections identification carries it to the sections of `ℐᵏ𝒢` over
the étale chart which the affine open cuts out. -/
theorem chartPushι_app_mem (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ)
    (Y : ((chartScheme A).Opens)ᵒᵖ)
    (x : (chartPush B S hS X (idealPowModule I k G) A).val.obj Y) :
    ((chartPushι B S hS X I G A k).val.app Y).hom x ∈
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
        (idealSheafDataOfChart B S hS X I hIc A) k
          (chartPush B S hS X G A)).toSubmodule.obj Y := by
  obtain ⟨V⟩ := Y
  have _hqc := isQuasicoherent_chartPush B S hS X G hGq A
  refine Eq.mpr (congrArg (fun P : (chartPush B S hS X G A).Submodule =>
      ((chartPushι B S hS X I G A k).val.app (op V)).hom x ∈ P.toSubmodule.obj (op V))
    (Stacks.AlgebraicGeometry.IdealPowerComparison.idealPowerMultiple_eq_idealPowSmul
      (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A))) ?_
  exact mem_obj_idealPowSmul_of_forall_chart B S hS X.1 X.2 I hIq G hGq k
    (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A)
    (fun W _ => openChartOfComparison B S hS X A W.1)
    (fun W _ => isAffine_chartScheme_openChartOfComparison B S hS X A W.2)
    (fun W _ => chartSectionsRingHom B S hS X A W.1)
    (fun W _ => surjective_chartSectionsRingHom B S hS X A W.1)
    (fun W _ => (chartPushEquiv B S hS X G A W.1).toAddEquiv)
    (fun W _ r y => chartPushEquiv_smul B S hS X G A W.1 r y)
    (fun W _ => map_chartSectionsRingHom_openChartIdeal B S hS X I A W.1)
    (fun W hW => chartPushι_app_mem_chartSubmodule B S hS X I G A k x W hW)

/-- **The factorization of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢` through `Iᵏ` times the chart
restriction of `𝒢`.**  This is the morphism along which a morphism out of `Iᵏ` times the chart
restriction — such as the one [Stacks, Tag 01YB] produces on the chart's scheme — becomes a
morphism out of the chart restriction of `ℐᵏ𝒢`. -/
def chartPushFactor (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ) :
    chartPush B S hS X (idealPowModule I k G) A ⟶
      Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) :=
  SheafOfModules.Submodule.factorThru _ (chartPushι B S hS X I G A k)
    (fun Y x => chartPushι_app_mem B S hS X I hIc G hIq hGq A k Y x)

/-- The factorization of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢`, composed with the inclusion of
`Iᵏ` times the chart restriction of `𝒢`, is that chart restriction. -/
theorem chartPushFactor_comp_ι (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ) :
    chartPushFactor B S hS X I hIc G hIq hGq A k ≫
        Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι
          (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
            (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A)) =
      chartPushι B S hS X I G A k :=
  SheafOfModules.Submodule.factorThru_ι _ (chartPushι B S hS X I G A k)
    (chartPushι_app_mem B S hS X I hIc G hIq hGq A k)

/-! ### Stacks 01YB on the chart's scheme -/

/-- **[Stacks, Tag 01YB] on the chart's scheme, applied to the transport of `θ`.**  On a chart
whose scheme is Noetherian the transported morphism is the restriction of a morphism out of `Iᵏ`
times the chart restriction of `𝒢`, for some `k`. -/
theorem exists_homRestrict_eq_chartThetaOver (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1)
    (hNo : _root_.AlgebraicGeometry.IsNoetherian (chartScheme A)) :
    ∃ (k : ℕ) (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
          chartPush B S hS X F A),
      Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
          (idealSheafDataOfChart B S hS X I hIc A)
          (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
            (idealSheafDataOfChart B S hS X I hIc A)) φ =
        chartThetaOver B S hS X I hIc G F θ A :=
  have _hno : _root_.AlgebraicGeometry.IsNoetherian (chartScheme A) := hNo
  have _hcoh := isCoherent_chartPush B S hS X G hG A hNo.toIsLocallyNoetherian
  have _hqc := isQuasicoherent_chartPush B S hS X F hFq A
  Stacks.AlgebraicGeometry.IdealPowerColimit.exists_homRestrict_eq
    (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A)
    (chartPush B S hS X F A) (chartThetaOver B S hS X I hIc G F θ A)

/-! ### Back to the slice of the small étale site of `X` -/

/-- `ℐᵏ𝒢` is quasi-coherent as soon as `ℐ` is and `𝒢` is coherent.  This is the hypothesis
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` needs at `ℐᵏ𝒢`, and it is what lets the
hypothesis `hIG` be spliced out of the statement of [Stacks, Tag 07UM]. -/
theorem isQuasicoherentOnSite_idealPowModule (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hG : IsCoherent B S hS X.1 X.2 G)
    (k : ℕ) : (idealPowModule I k G).IsQuasicoherentOnSite :=
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  (isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 I k G hG
    hIq).toIsQuasicoherentOnSite

/-- **A morphism out of `Iᵏ` times the chart restriction of `𝒢` on the chart's scheme, read as a
morphism of the restrictions to the slice of the small étale site of `X` at the chart.** -/
def chartAlpha (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hFq : F.IsQuasicoherentOnSite) (hG : IsCoherent B S hS X.1 X.2 G)
    (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    (idealPowModule I k G).over A ⟶ F.over A :=
  (chartSchemeModuleHomEquiv B S hS X (idealPowModule I k G) F
      (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) hFq A).symm
    ((chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
          (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).hom ≫
      chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k ≫ φ ≫
        (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv)

end AlgebraicGeometry.Space

end
