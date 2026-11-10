module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartData
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartForms
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections

/-!
# The Gysin map of [Stacks, Tag 0G83] on an equation chart

The local Gysin maps that [Stacks, Tag 0G86] glues are the maps of [Stacks, Tag 0G83] attached to
the equations of a chart. Tag 0G83 is available in this library only for *global* equations, so on
a chart `W` the whole situation is moved onto the open subscheme `W.toScheme`: the equations become
global sections of `𝒪_W` by `Stacks.Gysin.restrictEquations`, the closed immersion becomes
`i ∣_ W`, and the hypothesis becomes the global `Stacks.Gysin.IsCutOutByEquations` by
`Stacks.Gysin.IsCutOutByEquationsOn.morphismRestrict`.

This file performs that move and reads the resulting map back on the ambient scheme, where it is
the `loc` field of `Stacks.Gysin.GysinChartData` together with its three laws.

## Main definitions

* `Stacks.Gysin.chartGysin`: **the Gysin map of [Stacks, Tag 0G83] for the equations of a chart**,
  a morphism of sheaves of modules on the chart `W.toScheme`.
* `Stacks.Gysin.chartTargetHom`: the identification of its target with the restriction to the
  chart of `Stacks.Gysin.gysinTarget`, the one sheaf all the charts must land in.
* `Stacks.Gysin.srcIso`: the identification of `(i_*Ω^p_{Z/S})|_W` with the source of the chart
  Gysin map.
* `Stacks.Gysin.chartLocHom` and `Stacks.Gysin.chartLoc`: **the `loc` field of
  `Stacks.Gysin.GysinChartData`**, as a morphism of the restrictions to the chart and on the
  sections over an open of the ambient scheme contained in the chart.

## Main results

* `Stacks.Gysin.exists_eq_sum_of_isGeneratedByOn`: a section of an ideal sheaf generated on the
  chart is, near every point, a combination of the generators.
* `Stacks.Gysin.isCutOutByEquationsOn_of_isGeneratedByOn`: the equations of a chart cut out the
  closed subscheme there, in the sense `Stacks.Gysin.IsCutOutByEquationsOn`.
* `Stacks.Gysin.equationsClosedSet_eq_range` and
  `Stacks.Gysin.equationsClosedSet_restrictEquations`: **the common zero locus of the equations
  is the image of the closed subscheme.** This is what makes the target of the chart Gysin map,
  which is read on the zero locus of that chart's own equations, the same sheaf for every chart.
* `Stacks.Gysin.chartGysin_formula`: the Gysin formula of [Stacks, Tag 0G83] for the chart map.
* `Stacks.Gysin.chartLoc_add`, `chartLoc_smul`, `chartLoc_res`: the `loc_add`, `loc_smul` and
  `loc_res` fields of `Stacks.Gysin.GysinChartData`.
* `Stacks.Gysin.chartCls_eq_restrictSections`, with `chartCls_smul` and `chartCls_res`: the class
  map of a chart is read on sections by the same conjugation as the Gysin map of a chart.
* `Stacks.Gysin.globalSmul_comp_chartClsHom` and `Stacks.Gysin.chartCls_vanish`: **the
  `cls_vanish` field** — the chart class map kills a multiple of one of the chart's equations,
  and hence any form whose coefficient vanishes on the closed subscheme.
* `Stacks.Gysin.exists_changeOfEquations`: **the `matrix` and `equations_eq` data of
  `Stacks.Gysin.ChartComparison`**, over a covering by affine opens of an open contained in two
  charts, which is also the covering `Stacks.Gysin.GysinChartData.comparison` asks for.
* `Stacks.Gysin.chartLoc_subschemeFormPullback`: **the `loc_subschemeFormPullback` field** — the
  Gysin formula of [Stacks, Tag 0G83] for the local Gysin map of a chart, on sections, from
  `Stacks.Gysin.srcIso_hom_app_subschemeFormPullback`,
  `Stacks.Gysin.formRestriction_comp_chartGysin_comp_chartTargetHom` and
  `Stacks.Gysin.gysinWedgeHom_app_relativeDifferentialFormsRestrictIso`.

## Implementation notes

**Why the target is built from `supportCohomologyToPushforward`.** `Stacks.Gysin.chartTargetHom`
inverts `Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` rather than using
`Stacks.Perfect.GysinLocalCohomology.gysinTargetIso`. Those are two independently constructed
isomorphisms between the same pair of objects, in opposite directions, and no declaration asserts
that they are mutually inverse; using the first keeps the chain free of that unproved statement.

**What this file does not itself supply for `Stacks.Gysin.GysinChartData`.** One field,
`comparison`, and within it one clause: `ChartComparison.cls_det` for two *different* charts.
`Stacks.Gysin.chartCls_det` is [Stacks, Tag 0G7S] for two families of equations on one chart, and
reducing the two-chart statement to it needs the class map of [Stacks, Tag 0G7Q] to be local —
that `chartClsHom` of a chart `W`, restricted to a smaller `W'`, is `chartClsHom` of the chart
`W'` with the restricted equations.  **That statement is now proved**, as
`Stacks.Gysin.chartClsHom_homOfLE` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartClsImmersionComp.lean`, read on sections as
`Stacks.Gysin.chartCls_homOfLE`, and the clause it yields is `Stacks.Gysin.clsDetAcrossCharts` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataComparison.lean`.  Both of its halves hold
along the chart-to-chart leg `AlgebraicGeometry.Scheme.homOfLE`: the excision half is
`Stacks.Gysin.supportCohomologyRestrictIso_hom_homOfLE`, and the base change of
`Stacks.Perfect.SupportedFraction.supportedFractionSource`,
`Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinCocycleBaseChange.lean`, now holds along an
arbitrary open immersion, as does the whole Čech tower under it.  The implementation notes of
`ChartDataComparison.lean` say how the reduction goes; those of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Globalisation.lean` record the state of the locality
in full.

Since `Stacks.Gysin.gysinTarget` is spelled at the cohomology sheaf of `i_* R𝓗_Z` the transport is
the **derived** excision `Stacks.Gysin.supportCohomologyRestrictIso`, so no coherence between two
independently constructed excisions stands in the way, and the transitivity statement for that
excision over two nested opens is `Stacks.Gysin.supportCohomologyRestrictCompIso_hom` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionRestrictComp.lean`.

Of the four factors of `chartTargetHom`, three now have their compatibility with restriction:

* excision itself, `Stacks.Gysin.supportCohomologyRestrictIso`, by
  `Stacks.Gysin.supportCohomologyRestrictCompIso_hom` and `…_inv`, and — at the leg a nested
  chart of the *ambient* scheme actually meets — by
  `Stacks.Gysin.supportCohomologyRestrictIso_hom_homOfLE` and `…_inv_homOfLE` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataExcision.lean`;
* the identification of the coefficient module,
  `Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso`, by
  `…relativeDifferentialFormsRestrictIso_hom_comp` and `…_inv_comp` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartRestrictionComp.lean`, whose general form
  is `…toRestrictForms_comp`;
* the `eqToHom` of `Stacks.Gysin.supportCohomologySheaf_congr`, by
  `Stacks.Gysin.supportCohomologySheaf_congr_supportCohomologyRestrictCompIso` and `…_inv` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionCongr.lean`, together with its
  naturality in the coefficient module and its transitivity in the closed subset, which are what
  move it past the other two factors.

The fourth, `Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward`, has only
naturality in the complex; the `cls` layer does not go through it, which is why the determinant
rule across two charts does not need it.  The chart's equations themselves also restrict:
`Stacks.Gysin.restrictEquations_homOfLE` and
`Stacks.Gysin.equationsClosedSet_restrictEquations_homOfLE` of
`GysinChartRestrictionComp.lean` identify the smaller chart's equations and their zero locus.

**The structural obstruction is discharged: excision along
`AlgebraicGeometry.Scheme.homOfLE`.** `Stacks.Gysin.supportCohomologyRestrictCompIso_hom` is
stated for `W : Y.Opens` and `V : W.toScheme.Opens`, so its composite leg is `V.ι ≫ W.ι`.  A
nested chart is instead `W' ≤ W` in `X.Opens`, with leg `X.homOfLE e` and composite `W'.ι`, and
`X.homOfLE e` is not the canonical inclusion of an open of `W.toScheme`: `W'.toScheme` and
`(W.ι ⁻¹ᵁ W').toScheme` are only canonically *isomorphic*.
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataExcision.lean` supplies what the nested
chart needs: `Stacks.Gysin.supportCohomologyOpenImmersionIso` is excision along an **arbitrary**
open immersion of schemes, at the `restrictFunctor` spelling, and
`Stacks.Gysin.supportCohomologyRestrictIso_eq_openImmersionIso` says that at `W.ι` it is
`Stacks.Gysin.supportCohomologyRestrictIso W` — by `rfl`, since
`Stacks.Gysin.modulePullbackRestrictFunctorIso` is now Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` rather than the `jStar`
identification, which is the change that makes the two the same isomorphism instead of two
comparisons to be matched.  The nested-chart transitivity is then
`Stacks.Gysin.supportCohomologyRestrictIso_hom_homOfLE` and
`Stacks.Gysin.supportCohomologyRestrictIso_inv_homOfLE`, from the transitivity along a composite
of open immersions, `Stacks.Gysin.supportCohomologyOpenImmersionIso_hom_comp`, and the transport
along `AlgebraicGeometry.Scheme.homOfLE_ι`,
`Stacks.Gysin.supportCohomologyOpenImmersionIso_congr`.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.DifferentialsRestrict
open Stacks.Perfect.LocalCohomologyExcision
open Stacks.Perfect.SupportedFraction Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechSupportTransport

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### A section of an ideal sheaf generated on a chart is locally a combination -/

/-- Two successive restriction maps of `𝒪_X` along inclusions of opens compose to one. -/
private theorem presheaf_map_homOfLE_comp {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B)
    (a : Γ(X, A)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op a) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op a :=
  (presheaf_map_comp_apply _ _ _).trans (presheaf_map_congr _ _ a)

open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.RingedSpace in
/-- **A section of an ideal sheaf generated by `f₁, …, f_c` over an open `W` is, near every
point, a combination of the `f_j`.** This is `Stacks.AlgebraicGeometry.RegularIdealSheaf`'s
germwise description of the generated ideal sheaf, turned into the sectionwise statement the
charts of [Stacks, Tag 0G86] consume: the germ identity lives in a colimit, so its coefficients
come from sections over one common neighbourhood, and two sections with the same germ agree on a
smaller one. -/
theorem exists_eq_sum_of_isGeneratedByOn {X : Scheme.{u}}
    {J : (structureSheafModule X.toRingedSpace).Submodule} {W : X.Opens} {c : ℕ}
    {f : Fin c → Γ(X, W)} (hgen : IsGeneratedByOn X.toRingedSpace J W f)
    {V : X.Opens} (hVW : V ≤ W) (a : Γ(X, V)) (ha : a ∈ J.obj (op V)) (x : X) (hx : x ∈ V) :
    ∃ (V' : X.Opens) (hV' : V' ≤ V), x ∈ V' ∧ ∃ cc : Fin c → Γ(X, V'),
      X.presheaf.map (homOfLE hV').op a =
        ∑ l, cc l * X.presheaf.map (homOfLE (hV'.trans hVW)).op (f l) := by
  classical
  rw [hgen V hVW] at ha
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun (X.presheaf.stalk x)).mp
    ((mem_generatedIdealOn_iff W f V hVW a).mp ha x hx)
  obtain ⟨U₀, hxU₀, σ, hσ⟩ :=
    exists_common_germ (X := X.toLocallyRingedSpace) x γ Finset.univ
  have hxV₁ : x ∈ V ⊓ U₀ := ⟨hx, hxU₀⟩
  have hV₁V : V ⊓ U₀ ≤ V := inf_le_left
  have hV₁U₀ : V ⊓ U₀ ≤ U₀ := inf_le_right
  set A : Γ(X, V ⊓ U₀) := X.presheaf.map (homOfLE hV₁V).op a with hA
  set B : Γ(X, V ⊓ U₀) := ∑ l, X.presheaf.map (homOfLE hV₁U₀).op (σ l) *
    X.presheaf.map (homOfLE (hV₁V.trans hVW)).op (f l) with hB
  have hgermA : X.presheaf.germ (V ⊓ U₀) x hxV₁ A = X.presheaf.germ V x hx a :=
    X.presheaf.germ_res_apply (homOfLE hV₁V) x hxV₁ a
  have hgermB : X.presheaf.germ (V ⊓ U₀) x hxV₁ B = X.presheaf.germ V x hx a := by
    rw [hB, map_sum, ← hγ]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      hσ l (Finset.mem_univ l)]
    exact (smul_eq_mul _ _).symm
  obtain ⟨V', hxV', iA, iB, hAB⟩ :=
    X.presheaf.germ_eq x hxV₁ hxV₁ A B (hgermA.trans hgermB.symm)
  have hV'V₁ : V' ≤ V ⊓ U₀ := leOfHom iA
  refine ⟨V', hV'V₁.trans hV₁V, hxV',
    fun l => X.presheaf.map (homOfLE (hV'V₁.trans hV₁U₀)).op (σ l), ?_⟩
  have hL : X.presheaf.map iA.op A = X.presheaf.map (homOfLE (hV'V₁.trans hV₁V)).op a :=
    (presheaf_map_congr iA.op (homOfLE hV'V₁).op A).trans
      (presheaf_map_homOfLE_comp hV₁V hV'V₁ a)
  have hR : X.presheaf.map iB.op B =
      ∑ l, X.presheaf.map (homOfLE (hV'V₁.trans hV₁U₀)).op (σ l) *
        X.presheaf.map (homOfLE ((hV'V₁.trans hV₁V).trans hVW)).op (f l) := by
    rw [presheaf_map_congr iB.op (homOfLE hV'V₁).op B, hB, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, presheaf_map_homOfLE_comp, presheaf_map_homOfLE_comp]
  exact hL.symm.trans (hAB.trans hR)

open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- **The equations of a chart cut out the closed subscheme on that chart.** This is the
chart-local hypothesis `Stacks.Gysin.IsCutOutByEquationsOn` of [Stacks, Tag 0G83], assembled from
the two clauses the equation charts of [Stacks, Tag 0G86] come with: the equations lie in the
defining ideal, and they generate it over every open of the chart. -/
theorem isCutOutByEquationsOn_of_isGeneratedByOn (i : Z ⟶ X) {W : X.Opens} {c : ℕ}
    {f : Fin c → Γ(X, W)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)
    (hvanish : ∀ (V : X.Opens) (hV : V ≤ W) (j : Fin c),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (f j)) = 0) :
    IsCutOutByEquationsOn i W f where
  app_eq_zero j := by
    have h := hvanish W le_rfl j
    rwa [structurePresheaf_map_le_refl W (f j)] at h
  exists_eq_sum U hUW a ha x hx :=
    exists_eq_sum_of_isGeneratedByOn hgen hUW a
      ((mem_definingIdealOfHom_iff_app_eq_zero i U a).mpr ha) x hx

/-! ### The common zero locus of the equations is the closed subscheme -/

open Stacks.Perfect.CechDerivedSupport in
/-- **The common zero locus of a family of equations cutting out a closed subscheme is the image
of that subscheme.** The `⊇` half needs only that the equations vanish on the subscheme: their
preimages under a closed immersion are the basic opens of `0`, which are empty. The `⊆` half is
where the generation enters: away from the image, the unit section of `𝒪_X` vanishes on the
subscheme, so it is a combination of the equations near every such point, whence one of them has
invertible germ there.

This is the identification that lets the Gysin map of a chart, whose target is read on the
common zero locus of the chart's own equations, land in the one chart-independent sheaf
`Stacks.Gysin.gysinTarget`. -/
theorem equationsClosedSet_eq_range (j : Z ⟶ X) [IsClosedImmersion j] {c : ℕ}
    {g : Fin c → Γ(X, ⊤)} (hcut : IsCutOutByEquations j g) :
    equationsClosedSet g = Set.range j.base := by
  ext x
  constructor
  · intro hx
    by_contra hxr
    set U : X.Opens :=
      ⟨(Set.range j.base)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hxU : x ∈ U := hxr
    have hpre : j ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun z hz => absurd (Set.mem_range_self z) hz
    have hsub : Subsingleton Γ(Z, j ⁻¹ᵁ U) := by
      rw [hpre]
      infer_instance
    obtain ⟨V, hVU, hxV, cc, hcc⟩ :=
      hcut.exists_eq_sum U 1 (Subsingleton.elim _ _) x hxU
    rw [map_one] at hcc
    have hmem : ∀ l, X.presheaf.germ (⊤ : X.Opens) x trivial (g l)
        ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      intro l
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨l, (X.mem_basicOpen_top (g l) x).2 hu⟩)
    have hone : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      have h2 : (1 : X.presheaf.stalk x) =
          X.presheaf.germ V x hxV
            (∑ l, cc l * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (g l)) := by
        rw [← hcc, map_one]
      rw [h2, map_sum]
      refine Ideal.sum_mem _ fun l _ => ?_
      rw [map_mul, X.presheaf.germ_res_apply]
      exact Ideal.mul_mem_left _ _ (hmem l)
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top hone
  · rintro ⟨z, rfl⟩ hmem
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    have hz : z ∈ j ⁻¹ᵁ X.basicOpen (g l) := hl
    rw [Scheme.preimage_basicOpen_top, show j.appTop (g l) = 0 from hcut.appTop_eq_zero l,
      Scheme.basicOpen_zero] at hz
    exact hz

/-- The image of the part of a closed subscheme lying over a chart is the part of its image
lying over the chart. -/
theorem range_morphismRestrict_base (i : Z ⟶ X) (W : X.Opens) :
    Set.range (i ∣_ W).base = W.ι ⁻¹' Set.range i.base := by
  ext w
  simp only [Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(i ⁻¹ᵁ W).ι z, (morphismRestrict_base_coe i W z).symm⟩
  · rintro ⟨z, hz⟩
    have hzW : z ∈ i ⁻¹ᵁ W := by
      change i.base z ∈ W
      rw [hz]
      exact w.2
    exact ⟨⟨z, hzW⟩, Subtype.ext ((morphismRestrict_base_coe i W ⟨z, hzW⟩).trans hz)⟩

open Stacks.Perfect.CechDerivedSupport in
/-- **The common zero locus of the equations of a chart is the part of the closed subscheme
lying over the chart.** This is `Stacks.Gysin.equationsClosedSet_eq_range` for the restricted
closed immersion, read back on the chart. -/
theorem equationsClosedSet_restrictEquations (i : Z ⟶ X) [IsClosedImmersion i] (W : X.Opens)
    {c : ℕ} {f : Fin c → Γ(X, W)} (hcut : IsCutOutByEquationsOn i W f) :
    equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base :=
  (equationsClosedSet_eq_range (i ∣_ W) hcut.morphismRestrict).trans
    (range_morphismRestrict_base i W)

/-! ### The Gysin map of a chart -/

/-- The structural morphism of the part of the closed subscheme lying over a chart, written in
the two ways the two sides of the chart construction present it: as the restriction of `i ≫ π` to
the open `i ⁻¹ᵁ W`, and as the composite of the restricted closed immersion with the structural
morphism of the chart. -/
theorem chartComm (i : Z ⟶ X) (π : X ⟶ S) (W : X.Opens) :
    (i ⁻¹ᵁ W).ι ≫ (i ≫ π) = (i ∣_ W) ≫ (W.ι ≫ π) := by
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]

/-- **The Gysin map of [Stacks, Tag 0G83] for the equations of a chart.** The equations
`f : Fin c → Γ(X, W)` of the chart `W`, read as global sections of the open subscheme `W.toScheme`
by `Stacks.Gysin.restrictEquations`, cut out the closed subscheme `i ∣_ W` of `W.toScheme`, so
`AlgebraicGeometry.Scheme.Hom.gysinMap` applies there verbatim. -/
def chartGysin (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (W : X.Opens) {c : ℕ}
    (f : Fin c → Γ(X, W)) (p : ℕ) (hcut : IsCutOutByEquationsOn i W f) :
    (Scheme.Modules.pushforward (i ∣_ W)).obj
        (relativeDifferentialForms ((i ∣_ W) ≫ (W.ι ≫ π)) (p : ℤ)) ⟶
      pushforwardLocalCohomology (restrictEquations W f)
        (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ))) :=
  gysinMap (i ∣_ W) (W.ι ≫ π) (restrictEquations W f) p hcut.morphismRestrict

/-- **The Gysin formula of [Stacks, Tag 0G83] for the Gysin map of a chart.** On the restriction
to the closed subscheme of a relative `p`-form of the chart, the chart Gysin map is the fraction
class of `ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c`. -/
theorem chartGysin_formula (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (W : X.Opens) {c : ℕ}
    (f : Fin c → Γ(X, W)) (p : ℕ) (hcut : IsCutOutByEquationsOn i W f) :
    formRestriction (i ∣_ W) (W.ι ≫ π) (p : ℤ) ≫ chartGysin i π W f p hcut =
      gysinFormulaHom (W.ι ≫ π) (restrictEquations W f) (p : ℤ) :=
  formRestriction_comp_gysinMap (i ∣_ W) (W.ι ≫ π) (restrictEquations W f) p
    hcut.morphismRestrict

/-! ### The target of the chart Gysin map is the global target, restricted -/

/-- **The target of the Gysin map of a chart is the restriction to the chart of the global
target.** Four steps, none of which mentions the equations except through the closed subset they
cut out:

* the comparison `Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` of the two
  places at which the degree-`c` cohomology sheaf is taken, inverted, which turns the target of
  [Stacks, Tag 0G83] into the spelling of [Stacks, Tag 0G7Q] and [Stacks, Tag 0G7S];
* the identification `Ω^{p+c}_{W/S} ≅ (Ω^{p+c}_{X/S})|_W` of the coefficient module, applied
  through the functoriality of that sheaf in the coefficients;
* the transport of the supporting closed subset along `hgT`, which is
  `Stacks.Gysin.supportCohomologySheaf_congr`: the common zero locus of the chart's
  equations *is* the part of the closed subscheme lying over the chart, which is
  `Stacks.Gysin.equationsClosedSet_restrictEquations`. That transport is what makes all the
  charts land in one sheaf;
* excision itself, `Stacks.Gysin.supportCohomologyRestrictIso` — the **derived** excision of
  [Stacks, Tag 0G78] read on degree-`c` cohomology sheaves, at the very spelling of the
  cohomology sheaf that the previous three steps leave, so that no second construction of the
  local cohomology sheaf is involved.

It is built from `supportCohomologyToPushforward` and not from
`Stacks.Perfect.GysinLocalCohomology.gysinTargetIso`: those are two independently constructed
isomorphisms between the same pair of objects, in opposite directions, and no declaration asserts
that they are mutually inverse. -/
def chartTargetHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens)
    (g : Fin c → Γ(W.toScheme, ⊤))
    (hgT : equationsClosedSet g = W.ι ⁻¹' Set.range i.base) :
    pushforwardLocalCohomology g
        (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ))) ⟶
      (Scheme.Modules.restrictFunctor W.ι).obj (gysinTarget i π c p) :=
  (supportCohomologyToPushforward g
      (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ)))).inv ≫
    (supportCohomologySheafFunctor (isClosed_equationsClosedSet g) (c : ℤ)).map
        (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).inv ≫
      eqToHom (supportCohomologySheaf_congr hgT (isClosed_equationsClosedSet g)
          (isClosed_preimage_range_base i W) (c : ℤ)
          ((Scheme.Modules.restrictFunctor W.ι).obj
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) ≫
        (supportCohomologyRestrictIso W (isClosed_range_base i)
          (isClosed_preimage_range_base i W) (c : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv

/-! ### The local Gysin map of a chart, on sections -/

/-- **The source of the Gysin map of a chart is the restriction to the chart of the global
source.** The direct image `i_*Ω^p_{Z/S}` restricted to `W` is the direct image along `i ∣_ W` of
`Ω^p_{Z/S}` restricted to `i ⁻¹ᵁ W`, by
`Stacks.Modules.pushforwardRestrictFunctorIso`, and that restriction is the relative differential
forms of the restricted structural morphism, by
`Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIsoOfEq`. -/
def srcIso (i : Z ⟶ X) (π : X ⟶ S) (W : X.Opens) (p : ℕ) :
    Scheme.Modules.restrict (pushforwardRelativeForms i π (p : ℤ)) W.ι ≅
      (Scheme.Modules.pushforward (i ∣_ W)).obj
        (relativeDifferentialForms ((i ∣_ W) ≫ (W.ι ≫ π)) (p : ℤ)) :=
  (Stacks.Modules.pushforwardRestrictFunctorIso i W).app
      (relativeDifferentialForms (i ≫ π) (p : ℤ)) ≪≫
    (Scheme.Modules.pushforward (i ∣_ W)).mapIso
      (relativeDifferentialFormsRestrictIsoOfEq (i ≫ π) (i ⁻¹ᵁ W) (chartComm i π W) (p : ℤ))

/-- **The Gysin map of a chart, as a morphism of the restrictions to the chart of the global
source and target.** This is the Gysin map of [Stacks, Tag 0G83] for the chart's equations, read
between the two sheaves the gluing of [Stacks, Tag 0G86] needs: `srcIso` identifies its source
with `(i_*Ω^p_{Z/S})|_W`, and `Stacks.Gysin.chartTargetHom` its target with
`(i_*ℋ^c_Z(Ω^{p+c}_{X/S}))|_W`. -/
def chartLocHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base) :
    Scheme.Modules.restrict (pushforwardRelativeForms i π (p : ℤ)) W.ι ⟶
      Scheme.Modules.restrict (gysinTarget i π c p) W.ι :=
  (srcIso i π W p).hom ≫ chartGysin i π W f p hcut ≫
    chartTargetHom i π p W (restrictEquations W f) hgT

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `loc` field of `Stacks.Gysin.GysinChartData`**: the Gysin map of a chart, on the
sections over an open of the ambient scheme contained in the chart. This is `chartLocHom` read
through `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections`, which is the same conjugation
by the two restriction maps along `W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V` that `Stacks.Gysin.chartCls`
performs. -/
def chartLoc (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    Γ(gysinTarget i π c p, V) :=
  restrictSections (chartLocHom i π p W f hcut hgT) V hV x

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `loc_add` field**: the local Gysin map of a chart is additive. -/
theorem chartLoc_add (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (x y : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    chartLoc i π p W f hcut hgT V hV (x + y) =
      chartLoc i π p W f hcut hgT V hV x + chartLoc i π p W f hcut hgT V hV y :=
  restrictSections_add _ V hV x y

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `loc_smul` field**: the local Gysin map of a chart is `𝒪_X`-homogeneous. -/
theorem chartLoc_smul (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V))
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    chartLoc i π p W f hcut hgT V hV (r • x) = r • chartLoc i π p W f hcut hgT V hV x :=
  restrictSections_smul _ V hV r x

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `loc_res` field**: the local Gysin map of a chart commutes with restriction. -/
theorem chartLoc_res (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V V' : X.Opens) (hV' : V' ≤ V) (hV : V ≤ W)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    chartLoc i π p W f hcut hgT V' (hV'.trans hV)
        ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hV').op x) =
      (gysinTarget i π c p).presheaf.map (homOfLE hV').op
        (chartLoc i π p W f hcut hgT V hV x) :=
  restrictSections_res _ V' V hV' hV x

/-! ### The class map of a chart, read through the same conjugation -/

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `cls` field is the same conjugation as the `loc` field.** `Stacks.Gysin.chartCls` is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections` of `Stacks.Gysin.chartClsHom`: both read
a morphism of the restrictions to `W` on the sections over an open `V ≤ W`, using that the
sections of a restricted module over `W.ι ⁻¹ᵁ V` are the sections of the module over `V`. -/
theorem chartCls_eq_restrictSections (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W f hT hTf V hV y =
      restrictSections (chartClsHom i π p W f hT hTf) V hV y :=
  rfl

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The chart class map is `𝒪_X`-homogeneous.** -/
theorem chartCls_smul (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V))
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W f hT hTf V hV (r • y) = r • chartCls i π p W f hT hTf V hV y :=
  restrictSections_smul (chartClsHom i π p W f hT hTf) V hV r y

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The chart class map commutes with restriction.** -/
theorem chartCls_res (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V V' : X.Opens) (hV' : V' ≤ V) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W f hT hTf V' (hV'.trans hV)
        ((relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map
          (homOfLE hV').op y) =
      (gysinTarget i π (d + 1) p).presheaf.map (homOfLE hV').op
        (chartCls i π p W f hT hTf V hV y) :=
  restrictSections_res (chartClsHom i π p W f hT hTf) V' V hV' hV y

/-- **The chart class map kills a multiple of one of the chart's equations.** This is
`Stacks.Perfect.SupportedFraction.globalSmul_comp_supportedFractionSource` — the class map of
[Stacks, Tag 0G7Q] begins with the projection onto the cokernel of multiplication by the
equations — composed with the two transports of `Stacks.Gysin.chartClsHom`, which do not touch
the source. -/
theorem globalSmul_comp_chartClsHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) (l : Fin (d + 1)) :
    globalSmul (f l) ((Scheme.Modules.restrictFunctor W.ι).obj
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) ≫
        chartClsHom i π p W f hT hTf = 0 :=
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg
        (fun ψ => ψ ≫ (supportCohomologyRestrictIso W (isClosed_range_base i) hT
          ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)
        (globalSmul_comp_supportedFractionSource f
          ((Scheme.Modules.restrictFunctor W.ι).obj
            (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hT hTf l))
      Limits.zero_comp)

/-- **The chart class map kills a multiple of one of the chart's equations, on the sections over
an open of the chart.** This is `globalSmul_comp_chartClsHom` evaluated: the value of
`Stacks.Perfect.SupportedFraction.globalSmul` on sections is multiplication by the restriction
of the global function, by `Stacks.Perfect.SupportedFraction.globalSmul_app`. -/
theorem chartClsHom_app_equation (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) (l : Fin (d + 1))
    (V' : W.toScheme.Opens)
    (y : Γ((Scheme.Modules.restrictFunctor W.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))), V')) :
    (chartClsHom i π p W f hT hTf).app V'
        (W.toScheme.presheaf.map (homOfLE (show V' ≤ ⊤ from le_top)).op (f l) • y) = 0 := by
  refine Eq.trans (congrArg (fun φ => Scheme.Modules.Hom.app φ V' y)
    (globalSmul_comp_chartClsHom i π p W f hT hTf l)) ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

/-- The restriction to an open `V ≤ W` of one of a chart's equations, read as a function on the
chart by `Stacks.Gysin.restrictEquations` and carried back to `V` by `Stacks.Gysin.chartScalar`,
is just its restriction: all three maps are restriction maps of `𝒪_X` between opens of `X`. -/
theorem chartScalar_restrictEquations (W : X.Opens) {c : ℕ} (f : Fin c → Γ(X, W))
    {V : X.Opens} (hV : V ≤ W) (l : Fin c) :
    chartScalar W hV (restrictEquations W f l) = X.presheaf.map (homOfLE hV).op (f l) :=
  (presheaf_map_comp_apply _ _ _).trans
    ((presheaf_map_comp_apply _ _ _).trans (presheaf_map_congr _ _ (f l)))

/-- **The chart class map kills a multiple of one of the chart's equations**, on the sections
over an open `V` of the ambient scheme contained in the chart. This is
`chartClsHom_app_equation` conjugated by the two restriction maps of `Stacks.Gysin.chartCls`,
which is `Stacks.Gysin.chartCls_chartScalar_smul`. -/
theorem chartCls_equation_smul (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(X, W))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (l : Fin (d + 1))
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W (restrictEquations W f) hT hTf V hV
      (X.presheaf.map (homOfLE hV).op (f l) • y) = 0 := by
  rw [← chartScalar_restrictEquations W f hV l, chartCls_chartScalar_smul,
    chartClsHom_app_equation]
  exact map_zero _

open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- **The `cls_vanish` field of `Stacks.Gysin.GysinChartData`**: the chart class map kills a
form whose coefficient vanishes on the closed subscheme.

Such a coefficient is, near every point, a combination of the chart's equations — that is
`Stacks.Gysin.exists_eq_sum_of_isGeneratedByOn` — so over the members of a covering of the open
the value is a combination of the values on multiples of the equations, each of which vanishes
by `Stacks.Gysin.chartCls_equation_smul`. The target is a sheaf, so the value itself vanishes. -/
theorem chartCls_vanish (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(X, W))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V))
    (hr : (i.app V).hom r = 0) :
    chartCls i π p W (restrictEquations W f) hT hTf V hV (r • ω) = 0 := by
  classical
  have hmem : r ∈ (definingIdealOfHom i).obj (op V) :=
    (mem_definingIdealOfHom_iff_app_eq_zero i V r).mpr hr
  choose V' hle hxV cc hcc using fun x : ↥V =>
    exists_eq_sum_of_isGeneratedByOn hgen hV r hmem x.1 x.2
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨(gysinTarget i π (d + 1) p).presheaf, (gysinTarget i π (d + 1) p).isSheaf⟩ :
      TopCat.Sheaf Ab.{u} X))
    V' V (fun k => homOfLE (hle k))
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩) _ _ fun k => ?_
  rw [← chartCls_res, map_zero, Scheme.Modules.map_smul, hcc k, Finset.sum_smul, map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_smul, chartCls_smul, chartCls_equation_smul]
  exact smul_zero _

/-! ### The chart class map kills a multiple of an equation, on sections -/

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- The zero morphism of restrictions reads as the zero map on sections. -/
theorem restrictSections_zero {M N : X.Modules} {O : X.Opens}
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections (0 : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
      U h m = 0 := by
  change N.presheaf.map _ (restrictHomApp (0 : Scheme.Modules.restrict M O.ι ⟶
    Scheme.Modules.restrict N O.ι) (O.ι ⁻¹ᵁ U) _) = 0
  rw [restrictHomApp_apply]
  change N.presheaf.map _ (Scheme.Modules.Hom.app (0 : Scheme.Modules.restrict M O.ι ⟶
    Scheme.Modules.restrict N O.ι) (O.ι ⁻¹ᵁ U) _) = 0
  rw [Scheme.Modules.Hom.zero_app]
  exact map_zero _

/-! ### The Gysin formula of a chart, on sections -/

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The source half of the Gysin formula of a chart.** Restricting an ambient `p`-form to the
closed subscheme and reading the result on the chart is the same as restricting it to the chart
and then to the part of the closed subscheme lying over the chart: both are the pullback along
the composite `(i ⁻¹ᵁ W).ι ≫ i = (i ∣_ W) ≫ W.ι` of `Stacks.Gysin.chartComm`. -/
theorem srcIso_hom_app_subschemeFormPullback (i : Z ⟶ X) (π : X ⟶ S) (W : X.Opens) (p : ℕ)
    (U : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), U)) :
    Scheme.Modules.Hom.app (srcIso i π W p).hom (W.ι ⁻¹ᵁ U)
        ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map
          (homOfLE (W.ι.image_preimage_le U)).op (subschemeFormPullback i π (p : ℤ) U ω))
      = Scheme.Modules.Hom.app (formRestriction (i ∣_ W) (W.ι ≫ π) (p : ℤ)) (W.ι ⁻¹ᵁ U)
          (Scheme.Modules.Hom.app
            (relativeDifferentialFormsRestrictIso π W (p : ℤ)).hom (W.ι ⁻¹ᵁ U)
            ((relativeDifferentialForms π (p : ℤ)).presheaf.map
              (homOfLE (W.ι.image_preimage_le U)).op ω)) := by
  have hkU : ((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U = ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ U := by rw [morphismRestrict_ι]
  have hV₀ : (i ⁻¹ᵁ W).ι ''ᵁ ((i ∣_ W) ⁻¹ᵁ (W.ι ⁻¹ᵁ U)) ≤ i ⁻¹ᵁ U := by
    change (i ⁻¹ᵁ W).ι ''ᵁ (((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U) ≤ i ⁻¹ᵁ U
    rw [hkU]
    exact (i ⁻¹ᵁ W).ι.image_preimage_le (i ⁻¹ᵁ U)
  have hc2 : ((i ∣_ W) ≫ W.ι) ≫ π = ((i ∣_ W) ≫ (W.ι ≫ π)) ≫ 𝟙 S := by
    rw [Category.assoc, Category.comp_id]
  have hc3 : ((i ⁻¹ᵁ W).ι ≫ i) ≫ π = ((i ∣_ W) ≫ (W.ι ≫ π)) ≫ 𝟙 S := by
    rw [← morphismRestrict_ι, Category.assoc, Category.comp_id]
  have hnat := Hom_app_presheaf_map
    (relativeDifferentialFormsRestrictIsoOfEq (i ≫ π) (i ⁻¹ᵁ W) (chartComm i π W) (p : ℤ)).hom
    (show ((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ U from hkU.le)
    ((relativeDifferentialForms (i ≫ π) (p : ℤ)).presheaf.map
      (homOfLE ((i ⁻¹ᵁ W).ι.image_preimage_le (i ⁻¹ᵁ U))).op
      (subschemeFormPullback i π (p : ℤ) U ω))
  have hiso := relativeDifferentialFormsRestrictIsoOfEq_hom_app (i ≫ π) (i ⁻¹ᵁ W)
    (chartComm i π W) (p : ℤ) (i ⁻¹ᵁ U) (subschemeFormPullback i π (p : ℤ) U ω)
  have hcomp := relativeDifferentialFormsPullback_comp i (i ⁻¹ᵁ W).ι π (i ≫ π)
    ((i ∣_ W) ≫ (W.ι ≫ π)) (𝟙 S) (𝟙 S) (𝟙 S) (Category.comp_id (i ≫ π)).symm
    (chartComm i π W ▸ (Category.comp_id ((i ∣_ W) ≫ (W.ι ≫ π))).symm) hc3 (p : ℤ) U ω
  have hcongr := relativeDifferentialFormsPullback_congrMor
    (morphismRestrict_ι i W).symm π ((i ∣_ W) ≫ (W.ι ≫ π)) (𝟙 S) hc3 hc2 (p : ℤ) U ω
  have hR := relativeDifferentialFormsPullback_comp W.ι (i ∣_ W) π (W.ι ≫ π)
    ((i ∣_ W) ≫ (W.ι ≫ π)) (𝟙 S) (𝟙 S) (𝟙 S) (Category.comp_id (W.ι ≫ π)).symm
    (Category.comp_id ((i ∣_ W) ≫ (W.ι ≫ π))).symm hc2 (p : ℤ) U ω
  rw [relativeDifferentialFormsRestrictIso_hom_app]
  refine Eq.trans ?_ (hnat.symm.trans
    ((congrArg (fun z => (relativeDifferentialForms ((i ∣_ W) ≫ (W.ι ≫ π)) (p : ℤ)).presheaf.map
        (homOfLE (show ((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ U from hkU.le)).op z)
        hiso).trans
      ((congrArg (fun z => (relativeDifferentialForms ((i ∣_ W) ≫ (W.ι ≫ π)) (p : ℤ)).presheaf.map
          (homOfLE (show ((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ U from hkU.le)).op z)
          hcomp.symm).trans (hcongr.trans hR))))
  exact congrArg (Scheme.Modules.Hom.app
      (relativeDifferentialFormsRestrictIsoOfEq (i ≫ π) (i ⁻¹ᵁ W) (chartComm i π W) (p : ℤ)).hom
      (((i ∣_ W) ≫ W.ι) ⁻¹ᵁ U))
    ((modules_presheaf_map_comp_apply (M := relativeDifferentialForms (i ≫ π) (p : ℤ)) _ _ _).trans
      ((modules_presheaf_map_congr _ _ _).trans
        (modules_presheaf_map_comp_apply
          (M := relativeDifferentialForms (i ≫ π) (p : ℤ)) _ _ _).symm))

/-- **Transport of the class map of [Stacks, Tag 0G7Q] along the identification of the zero
locus of the equations with a given closed subset.** Substituting the closed subset reduces the
statement to the reflexivity case, in which the transport is the identity — the two proofs of
closedness being then two proofs of one proposition. -/
theorem supportedFractionSource_comp_eqToHom {Y : Scheme.{u}} {d : ℕ}
    (g : Fin (d + 1) → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent]
    {T : Set Y} (hT : IsClosed T) (hgT : equationsClosedSet g = T) {G : Y.Modules}
    (h : supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) ⟶ G) :
    supportedFractionSource g F (isClosed_equationsClosedSet g) subset_rfl ≫
        eqToHom (supportCohomologySheaf_congr hgT (isClosed_equationsClosedSet g) hT
          ((d + 1 : ℕ) : ℤ) F) ≫ h =
      supportedFractionSource g F hT hgT.le ≫ h := by
  subst hgT
  have hproof : hT = isClosed_equationsClosedSet g := rfl
  subst hproof
  rw [eqToHom_refl, Category.id_comp]

/-- **The Gysin formula of a chart, as an identity of morphisms on the chart.** Composing the
restriction of forms to the closed subscheme with the Gysin map of [Stacks, Tag 0G83] of the
chart's equations and with the identification of its target is wedging with the equation wedge
followed by the class map of [Stacks, Tag 0G7Q] of the chart.

Three inputs: `Stacks.Gysin.chartGysin_formula`, the Gysin formula of [Stacks, Tag 0G83];
`Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward`, which identifies
the two constructions of the class map of [Stacks, Tag 0G7Q]; and
`Stacks.Perfect.SupportedFraction.supportedFractionSource_natural`, the functoriality of
[Stacks, Tag 0G7T], which moves the identification of the coefficient module `Ω^{p+c}_{W/S}` with
`(Ω^{p+c}_{X/S})|_W` across the class map. -/
theorem formRestriction_comp_chartGysin_comp_chartTargetHom (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens) (f : Fin (d + 1) → Γ(X, W))
    (hcut : IsCutOutByEquationsOn i W f)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base) :
    formRestriction (i ∣_ W) (W.ι ≫ π) (p : ℤ) ≫ chartGysin i π W f p hcut ≫
        chartTargetHom i π p W (restrictEquations W f) hgT =
      gysinWedgeHom (W.ι ≫ π) (restrictEquations W f) (p : ℤ) ≫
        (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).inv ≫
          chartClsHom i π p W (restrictEquations W f) hT hgT.le := by
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  have : (relativeDifferentialForms (W.ι ≫ π)
      ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add (W.ι ≫ π) p (d + 1)
  have hFFC : formFractionClass (W.ι ≫ π) (restrictEquations W f)
        ((p : ℤ) + ((d + 1 : ℕ) : ℤ)) =
      supportedFractionSource (restrictEquations W f)
          (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))
          (isClosed_equationsClosedSet _) subset_rfl ≫
        (supportCohomologyToPushforward (restrictEquations W f)
          (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).hom :=
    (Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward
      (restrictEquations W f) _).symm
  rw [← Category.assoc, chartGysin_formula, gysinFormulaHom, Category.assoc, chartTargetHom,
    hFFC, Category.assoc, Iso.hom_inv_id_assoc]
  refine congrArg (fun φ => gysinWedgeHom (W.ι ≫ π) (restrictEquations W f) (p : ℤ) ≫ φ) ?_
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun φ => φ ≫
        (eqToHom (supportCohomologySheaf_congr hgT
            (isClosed_equationsClosedSet (restrictEquations W f))
            (isClosed_preimage_range_base i W) ((d + 1 : ℕ) : ℤ)
            ((Scheme.Modules.restrictFunctor W.ι).obj
              (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))) ≫
          (supportCohomologyRestrictIso W (isClosed_range_base i)
            (isClosed_preimage_range_base i W) ((d + 1 : ℕ) : ℤ)
            (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv))
        (supportedFractionSource_natural (restrictEquations W f)
          (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).inv
          (isClosed_equationsClosedSet (restrictEquations W f)) subset_rfl).symm).trans
      (Category.assoc _ _ _))) ?_
  exact congrArg (fun φ =>
      (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).inv ≫ φ)
    (supportedFractionSource_comp_eqToHom (restrictEquations W f) _
      (isClosed_preimage_range_base i W) hgT
      (supportCohomologyRestrictIso W (isClosed_range_base i)
        (isClosed_preimage_range_base i W) ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The `loc_subschemeFormPullback` field of `Stacks.Gysin.GysinChartData`: the Gysin formula
of [Stacks, Tag 0G83] for the local Gysin map of a chart.** On the restriction `ω̃|_Z` of an
ambient `p`-form over an open of the chart, the chart's Gysin map takes the value
`c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`.

Both sides are read on sections by the same conjugation, so the statement is the formula over
the corresponding open of the chart, where it is the composite of the source half
`Stacks.Gysin.srcIso_hom_app_subschemeFormPullback`, the Gysin formula
`Stacks.Gysin.formRestriction_comp_chartGysin_comp_chartTargetHom` and the wedge half
`Stacks.Gysin.gysinWedgeHom_app_relativeDifferentialFormsRestrictIso`. -/
theorem chartLoc_subschemeFormPullback (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ}
    (p : ℕ) (W : X.Opens) (f : Fin (d + 1) → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    chartLoc i π p W f hcut hgT V hV (subschemeFormPullback i π (p : ℤ) V ω) =
      chartCls i π p W (restrictEquations W f) hT hgT.le V hV
        (gysinWedgeOn π f (p : ℤ) hV ω) := by
  have hA1 := srcIso_hom_app_subschemeFormPullback i π W p V ω
  have hStep3 := congrArg (fun φ => Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app (relativeDifferentialFormsRestrictIso π W (p : ℤ)).hom
        (W.ι ⁻¹ᵁ V) ((relativeDifferentialForms π (p : ℤ)).presheaf.map
          (homOfLE (W.ι.image_preimage_le V)).op ω)))
    (formRestriction_comp_chartGysin_comp_chartTargetHom i π p W f hcut hT hgT)
  have hA4 := gysinWedgeHom_app_relativeDifferentialFormsRestrictIso π W f (p : ℤ) V hV ω
  have hinv := congrArg (fun φ => Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ V)
      ((relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map
        (homOfLE (W.ι.image_preimage_le V)).op (gysinWedgeOn π f (p : ℤ) hV ω)))
    (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).hom_inv_id
  refine congrArg ((gysinTarget i π (d + 1) p).presheaf.map
    (homOfLE (ι_image_chartOpen W hV).ge).op) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
    (chartGysin i π W f p hcut ≫ chartTargetHom i π p W (restrictEquations W f) hgT)
    (W.ι ⁻¹ᵁ V) z) hA1) ?_
  refine Eq.trans hStep3 ?_
  refine congrArg (Scheme.Modules.Hom.app
    (chartClsHom i π p W (restrictEquations W f) hT hgT.le) (W.ι ⁻¹ᵁ V)) ?_
  refine Eq.trans (congrArg (Scheme.Modules.Hom.app
    (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).inv
    (W.ι ⁻¹ᵁ V)) hA4) ?_
  exact hinv

/-! ### The change-of-equations matrix of two charts -/

open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- **The change-of-equations matrix of two charts, over a covering by affine opens of an open
contained in both.** This is the `matrix` and `equations_eq` data of
`Stacks.Gysin.ChartComparison`, together with the covering that
`Stacks.Gysin.GysinChartData.comparison` asks for and the affineness that makes
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen` apply.

Each equation of the second chart vanishes on the closed subscheme, so by
`Stacks.Gysin.exists_eq_sum_of_isGeneratedByOn` it is, near every point, a combination of the
equations of the first; the `c` neighbourhoods so obtained are intersected, and the result is
shrunk to an affine open, the affine opens being a basis. -/
theorem exists_changeOfEquations (i : Z ⟶ X) {Wa Wb : X.Opens} {c : ℕ}
    {fa : Fin c → Γ(X, Wa)} {fb : Fin c → Γ(X, Wb)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) Wa fa)
    (hvanish : ∀ (O : X.Opens) (hO : O ≤ Wb) (j : Fin c),
      (i.app O).hom (X.presheaf.map (homOfLE hO).op (fb j)) = 0)
    (V : X.Opens) (ha : V ≤ Wa) (hb : V ≤ Wb) :
    ∃ (V' : ↥V → X.Opens) (hle : ∀ k, V' k ≤ V),
      (∀ k, IsAffineOpen (V' k)) ∧
      (∀ k, ∃ A : Matrix (Fin c) (Fin c) Γ(X, V' k), ∀ j,
          X.presheaf.map (homOfLE ((hle k).trans hb)).op (fb j) =
            ∑ l, A j l * X.presheaf.map (homOfLE ((hle k).trans ha)).op (fa l)) ∧
      V ≤ ⨆ k, V' k := by
  classical
  have hstep : ∀ (x : ↥V) (j : Fin c), ∃ (U : X.Opens) (hU : U ≤ V), (x : X) ∈ U ∧
      ∃ cc : Fin c → Γ(X, U),
        X.presheaf.map (homOfLE hU).op (X.presheaf.map (homOfLE hb).op (fb j)) =
          ∑ l, cc l * X.presheaf.map (homOfLE (hU.trans ha)).op (fa l) :=
    fun x j => exists_eq_sum_of_isGeneratedByOn hgen ha _
      ((mem_definingIdealOfHom_iff_app_eq_zero i V _).mpr (hvanish V hb j)) x.1 x.2
  choose U hU hxU cc hcc using hstep
  have haff : ∀ x : ↥V, ∃ O : X.Opens, IsAffineOpen O ∧ (x : X) ∈ O ∧
      (O : Set X) ⊆ (V : Set X) ∩ ⋂ j : Fin c, (U x j : Set X) := by
    intro x
    obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hOsub⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show (x : X) ∈ (V : Set X) ∩ ⋂ j : Fin c, (U x j : Set X) from
          ⟨x.2, Set.mem_iInter.2 fun j => hxU x j⟩)
        (V.isOpen.inter (isOpen_iInter_of_finite fun j => (U x j).isOpen))
    exact ⟨O, hO, hxO, hOsub⟩
  choose O hOaff hxO hOsub using haff
  have hOV : ∀ x : ↥V, O x ≤ V := fun x _ hz => (hOsub x hz).1
  have hOU : ∀ (x : ↥V) (j : Fin c), O x ≤ U x j :=
    fun x j _ hz => Set.mem_iInter.1 (hOsub x hz).2 j
  refine ⟨O, hOV, hOaff,
    fun x => ⟨fun j l => X.presheaf.map (homOfLE (hOU x j)).op (cc x j l), fun j => ?_⟩,
    fun z hz => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxO ⟨z, hz⟩⟩⟩
  have hrest := congrArg (fun y => X.presheaf.map (homOfLE (hOU x j)).op y) (hcc x j)
  simp only [map_sum, map_mul, presheaf_map_homOfLE_comp] at hrest
  exact hrest

end Stacks.Gysin

end
