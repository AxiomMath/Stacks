module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocallySpannedDischarge
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation on the small étale site from finite presentation on the charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Finite presentation of `F` is recorded in two forms: on the small
étale site, `SheafOfModules.IsFinitePresentationOnSite` (Stacks 03DL (7)), and on the étale
scheme charts, `AlgebraicGeometry.Space.IsFinitePresentationOnCharts`.  The passage from the
first to the second is
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`; this file
proves the converse, so that the two forms agree for quasi-coherent modules.

The argument is the descent of a presentation along étale morphisms of affine schemes.  Over an
affine étale chart `U` whose sections `F(U)` form a finitely presented `𝒪_X(U)`-module, choose
generators `s₁, …, sₙ` of `F(U)` and generators `r₁, …, r_p` of the module of relations among
them.  The `sᵢ` generate `F` étale locally because `F` is cartesian on affine charts
(Stacks 03DX (2)).  A relation `∑ τᵢ sᵢ|_V = 0` over some `V ⟶ U` is, on each affine chart `P`
of `V`, a relation over `P` among the restrictions of the `sᵢ`, and the relations over `P` are
spanned by the restrictions of the relations over `U`: the comparison
`𝒪_X(P) ⊗_{𝒪_X(U)} F(U) ⟶ F(P)` is injective and tensor product is right exact
(`Module.BaseChange.mem_span_image_ker_of_liftBaseChange`).  No flatness is needed.  So the
`sᵢ` and `rₖ` form a finite global presentation of `F` on the slice at `U`, and the affine
charts cut out by the affine opens of any chart cover it.

## Main results

* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_of_moduleFinitePresentation`: over
  an affine étale chart whose sections are finitely presented, a module cartesian on affine
  charts has a finite global presentation on the slice.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_forall_affine_moduleFinitePresentation`:
  a module cartesian on affine charts whose sections over every affine étale chart are finitely
  presented is of finite presentation on the small étale site.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_forall_affine_moduleFinitePresentation`:
  for a quasi-coherent module the two conditions agree.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isFinitePresentationOnCharts`: **a
  quasi-coherent module of finite presentation on the étale scheme charts is of finite
  presentation on the small étale site.**
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_isFinitePresentationOnCharts`: the two
  readings of finite presentation agree for quasi-coherent modules.

## References

* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### A finite global presentation over an affine chart -/

/-- **Over an affine étale chart whose sections form a finitely presented module, a module
cartesian on affine charts has a finite global presentation on the slice at that chart.**

The generators are a finite generating family of the sections over the chart and the relations
are a finite generating family of the relations among them.  The generators generate locally by
`AlgebraicGeometry.Space.generates_of_span_eq_top`.  A relation over `V ⟶ U` is, on each affine
chart cut out by an affine open of `V`, a combination of the restricted relations over `U`, by
right exactness of the base change and injectivity of the comparison of Stacks 03DX (2). -/
theorem hasFiniteGlobalPresentation_over_of_moduleFinitePresentation
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (C : (smallEtaleRingedSite B S hS F hF).C)
    (hC : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj C))
    (hfp : Module.FinitePresentation (chartRing B S hS F hF C) (G.val.obj (op C))) :
    SheafOfModules.HasFiniteGlobalPresentation (G.over C) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := chartRing B S hS F hF C)
    (M := (G.val.obj (op C) : Type u))
  let bT := Fintype.linearCombination (chartRing B S hS F hF C) s
  have hbT : Function.Surjective bT := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hs
  obtain ⟨p, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.FinitePresentation.fg_ker bT hbT)
  have hrker : ∀ k, bT (r k) = 0 := fun k =>
    LinearMap.mem_ker.mp (hr ▸ Submodule.subset_span ⟨k, rfl⟩)
  refine _root_.SheafOfModules.hasFiniteGlobalPresentation_over_of_generates G C s r
    (fun k => ?_) (generates_of_span_eq_top G hG hC s hs) ?_
  · have h := hrker k
    rwa [Fintype.linearCombination_apply] at h
  intro V hV τ hτ
  refine ⟨Sieve.ofArrows
      (fun O : ULift.{u + 1} ((chartScheme V).affineOpens) => openChart B S hS F V O.down.1)
      (fun O => openChartInclusion B S hS F V O.down.1),
    SmallEtale.ofArrows_openChart_affineOpens_mem B S hS F V, ?_⟩
  intro D g hg
  obtain ⟨O, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  let P := openChart B S hS F V O.down.1
  let ι : P ⟶ V := openChartInclusion B S hS F V O.down.1
  have hPaff : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj P) :=
    isAffine_chartScheme_openChart B S hS F V O.down
  let φ : P ⟶ C := ι ≫ hV
  let := chartAlgebra (hF := hF) φ
  let := chartSectionsModule G φ
  have := chartSections_isScalarTower G φ
  have : IsScalarTower (chartRing B S hS F hF C) (chartRing B S hS F hF P)
      (Fin n → chartRing B S hS F hF P) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let rN := chartRestrictLinear G φ
  let bW := Fintype.linearCombination (chartRing B S hS F hF P) fun i => rN (s i)
  let rP : (Fin n → chartRing B S hS F hF C) →ₗ[chartRing B S hS F hF C]
      (Fin n → chartRing B S hS F hF P) := (Algebra.linearMap _ _).compLeft (Fin n)
  have hsq : ∀ q, rN (bT q) = bW (rP q) := by
    intro q
    change rN (Fintype.linearCombination _ s q) = Fintype.linearCombination _ _ (rP q)
    rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun l _ => map_smul rN (q l) (s l)
  have hPbij : Function.Bijective (rP.liftBaseChange (chartRing B S hS F hF P)) := by
    refine Module.BaseChange.bijective_liftBaseChange_of_basis
      (Pi.basisFun (chartRing B S hS F hF C) (Fin n))
      (Pi.basisFun (chartRing B S hS F hF P) (Fin n)) rP fun l => funext fun j => ?_
    change algebraMap (chartRing B S hS F hF C) (chartRing B S hS F hF P)
        (Pi.basisFun (chartRing B S hS F hF C) (Fin n) l j) =
      Pi.basisFun (chartRing B S hS F hF P) (Fin n) l j
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases hjl : j = l
    · subst hjl
      rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hjl, Pi.single_eq_of_ne hjl, map_zero]
  have hN : Function.Injective (rN.liftBaseChange (chartRing B S hS F hF P)) :=
    (hG C P hC hPaff φ).1
  -- The relation, restricted to `P`.
  let z : Fin n → chartRing B S hS F hF P := fun i => chartRestrict (hF := hF) ι (τ i)
  have hz : bW z = 0 := by
    change Fintype.linearCombination _ _ z = 0
    rw [Fintype.linearCombination_apply]
    have h0 := congrArg (chartRestrictLinear G ι) hτ
    rw [map_zero, map_sum] at h0
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h0
    refine Eq.trans ?_
      (chartRestrictLinear_smul G ι (τ i) (chartRestrictLinear G hV (s i))).symm
    exact congrArg (fun w => chartRestrict (hF := hF) ι (τ i) • w)
      (chartRestrictLinear_comp G hV ι (s i))
  have hzmem := Module.BaseChange.mem_span_image_ker_of_liftBaseChange bT bW rP rN hsq
    hPbij.2 hN hbT hz
  -- The image of the kernel is spanned by the images of the chosen relations.
  have hle : Submodule.span (chartRing B S hS F hF P)
        (rP '' (LinearMap.ker bT : Set (Fin n → chartRing B S hS F hF C))) ≤
      Submodule.span (chartRing B S hS F hF P) (Set.range fun k => rP (r k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [← hr] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
        rw [map_smul]
        exact Submodule.smul_of_tower_mem _ c ha
  obtain ⟨d', hd'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hzmem)
  refine ⟨fun k => chartRestrict (hF := hF) h (d' k), fun i => ?_⟩
  have hi := congrArg (fun w : Fin n → chartRing B S hS F hF P => chartRestrict (hF := hF) h (w i))
    hd'
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, map_mul] at hi
  change ∑ k, chartRestrict (hF := hF) h (d' k) *
      chartRestrict (hF := hF) ((h ≫ ι) ≫ hV) (r k i) =
    chartRestrict (hF := hF) (h ≫ ι) (τ i)
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Eq.trans hi ?_)
  · congr 1
  · change chartRestrict (hF := hF) h (chartRestrict (hF := hF) ι (τ i)) =
      chartRestrict (hF := hF) (h ≫ ι) (τ i)
    exact (RingHom.congr_fun (chartRestrict_comp (hF := hF) ι h) (τ i)).symm

/-! ### Finite presentation on the site from the sections over the affine charts -/

/-- **A module cartesian on affine charts whose sections over every affine étale chart form a
finitely presented module is of finite presentation on the small étale site.**  The covering of
each chart asked for by `SheafOfModules.IsFinitePresentationOnSite` is the family of charts cut
out by the affine opens of the chart's scheme. -/
theorem isFinitePresentationOnSite_of_forall_affine_moduleFinitePresentation
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (hfp : ∀ C : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj C) →
        Module.FinitePresentation (chartRing B S hS F hF C) (G.val.obj (op C))) :
    SheafOfModules.IsFinitePresentationOnSite G := by
  refine ⟨fun U => ⟨ULift.{u + 1} ((chartScheme U).affineOpens),
    fun O => openChart B S hS F U O.down.1,
    fun O => openChartInclusion B S hS F U O.down.1,
    SmallEtale.ofArrows_openChart_affineOpens_mem B S hS F U, fun O => ?_⟩⟩
  exact hasFiniteGlobalPresentation_over_of_moduleFinitePresentation B S hS F hF G hG _
    (isAffine_chartScheme_openChart B S hS F U O.down)
    (hfp _ (isAffine_chartScheme_openChart B S hS F U O.down))

/-- **For a quasi-coherent module, finite presentation on the small étale site is finite
presentation of the sections over every affine étale chart.**  The forward implication is
`AlgebraicGeometry.Space.module_finitePresentation_sections_of_isFinitePresentationOnSite`, where
faithfully flat descent happens; the converse is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_forall_affine_moduleFinitePresentation`,
quasi-coherence giving cartesianness by Stacks 03DX (2). -/
theorem isFinitePresentationOnSite_iff_forall_affine_moduleFinitePresentation
    (G : Modules.{u, u} B S hS F hF) (hG : G.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentationOnSite G ↔
      ∀ C : (smallEtaleRingedSite B S hS F hF).C,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj C) →
          Module.FinitePresentation (chartRing B S hS F hF C) (G.val.obj (op C)) :=
  ⟨fun hfp => module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp,
    isFinitePresentationOnSite_of_forall_affine_moduleFinitePresentation B S hS F hF G
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG)⟩

/-! ### Finite presentation on the site from finite presentation on the charts -/

variable {B S hS} (X : AlgebraicSpaces B S hS)

/-- **The sections over an affine étale chart of a quasi-coherent module whose restriction to
that chart is of finite presentation form a finitely presented module.**  The sections are the
global sections of the chart restriction, linearly over the functions on the chart's scheme
(`AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`), and on an affine scheme the global
sections of a module of finite presentation are finitely presented. -/
theorem moduleFinitePresentation_sections_of_isFinitePresentation_restrictToChart
    (M : Modules.{u, u} B S hS X.1 X.2)
    (C : SmallEtale B S hS X.1)
    (hC : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj C))
    (hfp : (restrictToChart B S hS X.2 M C).IsFinitePresentation) :
    Module.FinitePresentation (chartRing B S hS X.1 X.2 C) (M.val.obj (op C)) := by
  have : IsAffine (chartScheme C) := hC
  have : (chartRestrictionSheaf B S hS X M C).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso hfp
      (restrictToChartIsoChartRestrictionSheaf B S hS X M C)
  have := Stacks.AlgebraicGeometry.ModuleLimits.finitePresentation_sectionsTop
    (chartRestrictionSheaf B S hS X M C)
  have : Module.FinitePresentation Γ(chartScheme C, ⊤) (M.val.obj (op C)) :=
    Module.FinitePresentation.of_equiv (chartRestrictionSheafTopEquiv B S hS X M C).symm
  exact this

/-- **A quasi-coherent module of finite presentation on the étale scheme charts is of finite
presentation on the small étale site.**  This is the converse of
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`: the sections
over every affine étale chart are finitely presented, and a finite presentation of them descends
to a finite global presentation on the slice at the chart. -/
theorem isFinitePresentationOnSite_of_isFinitePresentationOnCharts
    (M : Modules.{u, u} B S hS X.1 X.2) (hqc : M.IsQuasicoherentOnSite)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 M) :
    SheafOfModules.IsFinitePresentationOnSite M :=
  (isFinitePresentationOnSite_iff_forall_affine_moduleFinitePresentation B S hS X.1 X.2 M hqc).2
    fun C hC =>
      moduleFinitePresentation_sections_of_isFinitePresentation_restrictToChart X M C hC
        (hfp C)

/-- **For a quasi-coherent module, finite presentation on the small étale site is finite
presentation on the étale scheme charts.**  This is the property "of finite presentation" of the
section of Stacks 05VR on properties of modules on an algebraic space: it may be read on the
small étale site, or on every étale scheme chart, where for a quasi-coherent module it is the
property of the corresponding module on the scheme (the scheme case being Stacks 05VG). -/
@[stacks 05VR "of finite presentation: for a quasi-coherent module on an algebraic space, \
finite presentation on the small etale site is finite presentation of its restriction to every \
etale scheme chart, read on the Zariski site of the chart (items (2) and (4) of the section)"]
theorem isFinitePresentationOnSite_iff_isFinitePresentationOnCharts
    (M : Modules.{u, u} B S hS X.1 X.2) (hqc : M.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentationOnSite M ↔ IsFinitePresentationOnCharts B S hS X.2 M :=
  ⟨isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X M hqc,
    isFinitePresentationOnSite_of_isFinitePresentationOnCharts X M hqc⟩

end AlgebraicGeometry.Space

end
