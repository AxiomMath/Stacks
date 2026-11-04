module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartTransport

/-!
# The chart factorization of `ℐᵏ𝒢 ⟶ 𝒢` is an isomorphism

Let `X` be an algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a sheaf of ideals, let `𝒢` be
an `𝒪_X`-module and let `A` be an étale scheme chart of `X`.  The morphism
`AlgebraicGeometry.Space.chartPushFactor` factors the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢` through
`Iᵏ` times the chart restriction of `𝒢`, where `I` is the Zariski sheaf of ideals which the chart
inherits.  This file proves that it is an **isomorphism**, which is what Step 3 of
[Stacks, Tag 07UM] needs in order to compare the direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` with the
direct system of the first display of [Stacks, Tag 01YB] on the chart's scheme.

The missing inclusion is `Iᵏ · (chart restriction of 𝒢) ⊆ chart restriction of ℐᵏ𝒢`, and it is
assembled from two ingredients.

**The semilinear transport.**  The comparison of the sections of the chart restriction of `𝒢`
over a Zariski open with the sections of `𝒢` over the étale chart which that open cuts out is
only *semilinear*, over the surjective ring map
`AlgebraicGeometry.Space.chartSectionsRingHom`.  Membership in `J ^ k • ⊤` is carried *forward*
along such a comparison onto membership in `(J.map g) ^ k • ⊤`, and that is the converse of
`Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top`.  This direction needs neither
surjectivity of the ring map nor injectivity of the comparison: it is the image of a product
under an additive map which turns the scalars of the source into scalars of the target.

**The covering sieve.**  A cover of a Zariski open of the chart's scheme by opens induces a
covering sieve of `AlgebraicGeometry.Space.openChartOfComparison` of that open in the small étale
site of `X`, so a statement proved at the affine opens of the chart's scheme propagates to a
general open on the *site* side.  This is what replaces the sheaf condition of `ℐᵏ𝒢` at the
chart.

## Main results

* `Stacks.Submodule.mem_map_pow_smul_top_of_mem_pow_smul_top`: **membership in `J ^ k • ⊤` is
  carried forward along a semilinear additive map.**
* `AlgebraicGeometry.Space.mem_pow_chartSectionIdeal_smul_top_of_mem_pow_ideal_smul_top` and
  `AlgebraicGeometry.Space.mem_chartSubmodule_of_mem_pow_ideal_smul_top`: **the semilinear
  transport at a chart** — the second is the transport of
  `AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule` along
  `AlgebraicGeometry.Space.chartSectionsRingHom`.
* `AlgebraicGeometry.Space.SmallEtale.mem_topology_openChartOfComparison_of_forall_nbhd`,
  `AlgebraicGeometry.Space.SmallEtale.ofArrows_openChartOfComparisonHom_mem_topology` and
  `AlgebraicGeometry.Space.SmallEtale.mem_topology_openChartOfComparison_of_forall_affineOpens`:
  **a cover of a Zariski open of the chart's scheme induces a covering sieve of the étale chart
  it cuts out.**
* `AlgebraicGeometry.Space.mem_chartSubmodule_idealPowSubmodule_of_forall_affineOpens`: the
  covering sieve applied to the local membership of `ℐᵏ𝒢`.
* `AlgebraicGeometry.Space.mem_chartSubmodule_idealPowSubmodule_of_mem_idealPowerMultiple`: **the
  two ingredients together** — a section of `Iᵏ` times the chart restriction of `𝒢` over a
  Zariski open of the chart's scheme is a section of the chart restriction of `ℐᵏ𝒢`, which is the
  inclusion `AlgebraicGeometry.Space.chartPushι_app_mem` lacks.
* `AlgebraicGeometry.Space.bijective_chartPushFactor_val_app`,
  `AlgebraicGeometry.Space.isIso_chartPushFactor` and
  `AlgebraicGeometry.Space.chartPushFactorIso`: **`AlgebraicGeometry.Space.chartPushFactor` is an
  isomorphism.**

## Implementation notes

**Only the formal half of the affine-chart description of `ℐᵏ𝒢` is used.**  The hard inclusion
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_le_pow_chartSectionIdeal_smul_top` —
and hence the affineness of the chart, the quasi-coherence of `ℐ` and the faithfully flat descent
behind it — is what the *other* direction of the factorization needs.  The direction proved here
only needs `AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule`, which is
formal, so no affineness and no quasi-coherence of `ℐ` enters the statements below.  Affineness
of the opens of the chart's scheme is still used, but only to *test* membership in the
scheme-side `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`, which is built from
affine-local data.

**Local membership is taken from the product, not from the sheaf condition.**  Instead of the
`isSheaf` field of `ℐᵏ𝒢` the proof uses `AlgebraicGeometry.Space.mem_idealPowSmul_of_sieve`,
whose hypothesis is phrased with `AlgebraicGeometry.Space.chartRestrictLinear` and the objectwise
product `Iᵏ(·) · 𝒢(·)`.  That keeps every step inside the chart-sections API and never unfolds
the underlying subfunctor of the submodule.

**The isomorphism is obtained objectwise.**  `AlgebraicGeometry.Space.chartPushFactor` is a
`SheafOfModules.Submodule.factorThru`, so its component over a Zariski open is a codomain
restriction of the component of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢`, which is an inclusion of a
submodule; injectivity is therefore formal and surjectivity is exactly the missing membership
statement.  `Stacks.SheafOfModules.isIso_of_bijective_val_app` turns that into an `IsIso`, the
forgetful functor to presheaves of modules reflecting isomorphisms.

No declaration here carries a `stacks` tag: these are inputs to Stacks 07UM, not clauses of it.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe v v₁ u₁ u m

namespace Stacks.Submodule

variable {R R' : Type*} [CommRing R] [CommRing R'] {M M' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']

/-- **Membership in `J ^ k • ⊤` is carried forward along a semilinear additive map.**  If
`e : M →+ M'` turns the scalars of `R` into scalars of `R'` along `g : R →+* R'` and `x` lies in
`J ^ k` times everything, then `e x` lies in `(J.map g) ^ k` times everything.

This is the converse of `Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top`, and unlike
that direction it needs neither surjectivity of `g` nor injectivity of `e`: a generator
`r • y` of `J ^ k • ⊤` is sent to `g r • e y`, and `g r` lies in `(J.map g) ^ k` because `g`
carries `J ^ k` onto it. -/
theorem mem_map_pow_smul_top_of_mem_pow_smul_top (g : R →+* R') (e : M →+ M')
    (he : ∀ (r : R) (x : M), e (r • x) = g r • e x) (J : Ideal R) (k : ℕ)
    {x : M} (hx : x ∈ J ^ k • (⊤ : Submodule R M)) :
    e x ∈ (J.map g) ^ k • (⊤ : Submodule R' M') := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun a b ha hb => ?_)
  · rw [he r y]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem g hr
  · rw [map_add]
    exact Submodule.add_mem _ ha hb

end Stacks.Submodule

namespace Stacks.PresheafOfModules

/-- **A morphism of presheaves of modules whose components are bijective is an isomorphism.**
The objectwise inverses are automatically natural, by
`CategoryTheory.PresheafOfModules.isoMk`. -/
theorem isIso_of_bijective_app {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : _root_.PresheafOfModules.{v} R} (f : M ⟶ N)
    (h : ∀ X : Cᵒᵖ, Function.Bijective (f.app X)) : IsIso f := by
  have hiso : ∀ X : Cᵒᵖ, IsIso (f.app X) :=
    fun X => (ConcreteCategory.isIso_iff_bijective (f.app X)).2 (h X)
  have he : (_root_.PresheafOfModules.isoMk (fun X => @asIso _ _ _ _ (f.app X) (hiso X))
      (fun _ _ g => f.naturality g)).hom = f := by
    ext1 X
    rfl
  exact he ▸ inferInstance

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

/-- **A morphism of sheaves of modules whose components are bijective is an isomorphism.**  The
forgetful functor to presheaves of modules is fully faithful, hence reflects isomorphisms. -/
theorem isIso_of_bijective_val_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N)
    (h : ∀ X : Cᵒᵖ, Function.Bijective (f.val.app X)) : IsIso f :=
  have : IsIso ((_root_.SheafOfModules.forget R).map f) :=
    Stacks.PresheafOfModules.isIso_of_bijective_app f.val h
  isIso_of_reflects_iso f (_root_.SheafOfModules.forget R)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

/-! ### The semilinear transport at a chart -/

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A section lying in `J ^ k` times everything has its chart comparison in the `k`-th power of
the ideal of sections of `ℐ` over the étale chart.**

The data is the étale chart `P` which the open `V` of the chart's scheme cuts out, the ring map
`g` comparing the functions on `V` with the sections of `𝒪_F` over `P`, the additive comparison
`e` of the sections of the module on `V` with the sections of `𝒢` over `P`, which is semilinear
over `g`, and an ideal `J` of the functions on `V` carried by `g` onto the ideal of sections of
`ℐ` over `P`.  They are parameters with equations rather than the canonical composites, so that
an instantiation matches the conclusion without a definitional check of the whole chart chain.

No surjectivity of `g`, no injectivity of `e`, no affineness of the chart and no
quasi-coherence is needed: this is
`Stacks.Submodule.mem_map_pow_smul_top_of_mem_pow_smul_top` read through the equation `hJ`.  The
comparison is therefore taken as an additive map and not as the additive isomorphism which
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` supplies — only the semilinearity is used. -/
theorem mem_pow_chartSectionIdeal_smul_top_of_mem_pow_ideal_smul_top
    (ℐ : IdealSheaves B S hS F hF) (𝒢 : Modules.{u, u} B S hS F hF) (k : ℕ)
    {T : Scheme.{u}} (Mc : T.Modules) {V : T.Opens}
    (P : SmallEtale B S hS F)
    (g : Γ(T, V) →+* chartRing B S hS F hF P)
    (e : Γ(Mc, V) →+ 𝒢.val.obj (op P))
    (he : ∀ (r : Γ(T, V)) (y : Γ(Mc, V)), e (r • y) = g r • e y)
    (J : Ideal Γ(T, V)) (hJ : Ideal.map g J = chartSectionIdeal B S hS F hF ℐ P)
    {x : Γ(Mc, V)} (hx : x ∈ J ^ k • (⊤ : Submodule Γ(T, V) Γ(Mc, V))) :
    e x ∈ chartSectionIdeal B S hS F hF ℐ P ^ k •
      (⊤ : Submodule (chartRing B S hS F hF P) (𝒢.val.obj (op P))) := by
  rw [← hJ]
  exact Stacks.Submodule.mem_map_pow_smul_top_of_mem_pow_smul_top g e he J k hx

/-- **The semilinear transport of
`AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule` along the composite
scalar map of a chart**: a section lying in `J ^ k` times everything has its chart comparison in
the sections of `ℐᵏ𝒢` over the étale chart.

This is the converse direction of
`AlgebraicGeometry.Space.mem_pow_ideal_smul_top_of_mem_chartSubmodule`.  It carries neither the
surjectivity of the ring map, nor the affineness of the chart, nor any quasi-coherence: those are
the hypotheses of the affine-chart *equality*, and only its formal inclusion is used here. -/
theorem mem_chartSubmodule_of_mem_pow_ideal_smul_top
    (ℐ : IdealSheaves B S hS F hF) (𝒢 : Modules.{u, u} B S hS F hF) (k : ℕ)
    {T : Scheme.{u}} (Mc : T.Modules) {V : T.Opens}
    (P : SmallEtale B S hS F)
    (g : Γ(T, V) →+* chartRing B S hS F hF P)
    (e : Γ(Mc, V) →+ 𝒢.val.obj (op P))
    (he : ∀ (r : Γ(T, V)) (y : Γ(Mc, V)), e (r • y) = g r • e y)
    (J : Ideal Γ(T, V)) (hJ : Ideal.map g J = chartSectionIdeal B S hS F hF ℐ P)
    {x : Γ(Mc, V)} (hx : x ∈ J ^ k • (⊤ : Submodule Γ(T, V) Γ(Mc, V))) :
    e x ∈ chartSubmodule B S hS F hF (idealPowSubmodule ℐ k 𝒢) P :=
  pow_chartSectionIdeal_smul_top_le_chartSubmodule B S hS F hF ℐ k P
    (mem_pow_chartSectionIdeal_smul_top_of_mem_pow_ideal_smul_top B S hS F hF ℐ 𝒢 k Mc P g e he
      J hJ hx)

/-- The `k`-th power of the ideal of sections of `ℐ` times everything sits inside the objectwise
product `ℐᵏ(P) · 𝒢(P)`, the submodule whose local membership defines `ℐᵏ𝒢`.  An honest `k`-fold
product of sections of `ℐ` is a section of `ℐᵏ`, and all of `𝒢(P)` is the sections of the top
submodule. -/
theorem pow_chartSectionIdeal_smul_top_le_chartIdealPow_smul
    (ℐ : IdealSheaves B S hS F hF) (𝒢 : Modules.{u, u} B S hS F hF) (k : ℕ)
    (P : SmallEtale B S hS F) :
    chartSectionIdeal B S hS F hF ℐ P ^ k •
        (⊤ : Submodule (chartRing B S hS F hF P) (𝒢.val.obj (op P)))
      ≤ chartIdealPow B S hS F hF ℐ k P •
        chartSubmodule B S hS F hF (⊤ : 𝒢.Submodule) P :=
  Submodule.smul_mono (pow_chartSectionIdeal_le_chartIdealPow B S hS F hF ℐ k P)
    (fun z _ => Stacks.SheafOfModules.mem_top_obj z)

end Transport

/-! ### Covering sieves of the chart cut out by a Zariski open -/

section Sieves

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **A sieve of the étale chart cut out by a Zariski open of a chart's scheme is covering as soon
as every point of that open has a neighbourhood inside it whose induced morphism of charts the
sieve contains.**

The scheme of `AlgebraicGeometry.Space.openChartOfComparison … A V` is the open subscheme `V` and
the morphism of schemes underlying
`AlgebraicGeometry.Space.openChartOfComparisonHom … A h` is the inclusion of open subschemes, both
definitionally, so the pointwise criterion
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range` reduces the covering
condition to a statement about points of the chart's scheme. -/
theorem SmallEtale.mem_topology_openChartOfComparison_of_forall_nbhd
    (A : SmallEtale B S hS X.1) {V : (chartScheme A).Opens}
    (T : Sieve (openChartOfComparison B S hS X A V))
    (hT : ∀ x : chartScheme A, x ∈ V → ∃ (W : (chartScheme A).Opens) (hWV : W ≤ V),
      x ∈ W ∧ T (openChartOfComparisonHom B S hS X A hWV)) :
    T ∈ SmallEtale.topology B S hS X.1 (openChartOfComparison B S hS X A V) := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro z
  obtain ⟨W, hWV, hzW, hTW⟩ := hT z.1 z.2
  refine ⟨openChartOfComparison B S hS X A W, openChartOfComparisonHom B S hS X A hWV, hTW,
    ⟨⟨z.1, hzW⟩, ?_⟩⟩
  exact ((chartScheme A).homOfLE_apply' hWV z.1 hzW).trans (Subtype.ext rfl)

/-- **A cover of a Zariski open of a chart's scheme by opens induces a covering sieve of the étale
chart which that open cuts out.**  This is the statement which lets a property proved at the
charts of a family of opens covering `V` propagate to the chart cut out by `V` itself, on the
site side rather than the scheme side. -/
theorem SmallEtale.ofArrows_openChartOfComparisonHom_mem_topology
    (A : SmallEtale B S hS X.1) {V : (chartScheme A).Opens} {ι : Type*}
    (W : ι → (chartScheme A).Opens) (hWV : ∀ i, W i ≤ V) (hcov : V ≤ ⨆ i, W i) :
    Sieve.ofArrows (fun i => openChartOfComparison B S hS X A (W i))
        (fun i => openChartOfComparisonHom B S hS X A (hWV i))
      ∈ SmallEtale.topology B S hS X.1 (openChartOfComparison B S hS X A V) := by
  refine mem_topology_openChartOfComparison_of_forall_nbhd B S hS X A _ fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov hx)
  exact ⟨W i, hWV i, hi, Sieve.ofArrows_mk _ _ i⟩

/-- **A sieve of the étale chart cut out by a Zariski open of a chart's scheme is covering as soon
as it contains the morphism induced by every affine open inside that open.**  The affine opens of
a scheme form a basis, so this is the covering criterion in the form in which the affine-local
statements of the chart's scheme are available. -/
theorem SmallEtale.mem_topology_openChartOfComparison_of_forall_affineOpens
    (A : SmallEtale B S hS X.1) {V : (chartScheme A).Opens}
    (T : Sieve (openChartOfComparison B S hS X A V))
    (hT : ∀ (W : (chartScheme A).affineOpens) (hW : W.1 ≤ V),
      T (openChartOfComparisonHom B S hS X A hW)) :
    T ∈ SmallEtale.topology B S hS X.1 (openChartOfComparison B S hS X A V) := by
  refine mem_topology_openChartOfComparison_of_forall_nbhd B S hS X A T fun x hx => ?_
  obtain ⟨W, hWmem, hxW, hWV⟩ :=
    Opens.isBasis_iff_nbhd.mp (chartScheme A).isBasis_affineOpens hx
  exact ⟨W, hWV, hxW, hT ⟨W, hWmem⟩ hWV⟩

/-! ### The sections of `ℐᵏ𝒢` over the chart cut out by a Zariski open -/

/-- **A section of `𝒢` over the étale chart cut out by a Zariski open of a chart's scheme which
lies in the objectwise product `ℐᵏ(·) · 𝒢(·)` over the chart of every affine open inside it is a
section of `ℐᵏ𝒢`.**

Membership in `ℐᵏ𝒢` is local, so it is tested on a covering sieve
(`AlgebraicGeometry.Space.mem_idealPowSmul_of_sieve`), and the sieve of arrows along which the
section restricts into the objectwise product is covering by
`AlgebraicGeometry.Space.SmallEtale.mem_topology_openChartOfComparison_of_forall_affineOpens`.
Nothing beyond the data is assumed. -/
theorem mem_chartSubmodule_idealPowSubmodule_of_forall_affineOpens
    (ℐ : IdealSheaves B S hS X.1 X.2) (𝒢 : Modules.{u, u} B S hS X.1 X.2) (k : ℕ)
    (A : SmallEtale B S hS X.1) {V : (chartScheme A).Opens}
    (x : 𝒢.val.obj (op (openChartOfComparison B S hS X A V)))
    (h : ∀ (W : (chartScheme A).affineOpens) (hW : W.1 ≤ V),
      chartRestrictLinear 𝒢 (openChartOfComparisonHom B S hS X A hW) x
        ∈ chartIdealPow B S hS X.1 X.2 ℐ k (openChartOfComparison B S hS X A W.1) •
          chartSubmodule B S hS X.1 X.2 (⊤ : 𝒢.Submodule)
            (openChartOfComparison B S hS X A W.1)) :
    x ∈ chartSubmodule B S hS X.1 X.2 (idealPowSubmodule ℐ k 𝒢)
      (openChartOfComparison B S hS X A V) := by
  let R : Sieve (openChartOfComparison B S hS X A V) :=
    { arrows := fun Y f => chartRestrictLinear 𝒢 f x ∈
        chartIdealPow B S hS X.1 X.2 ℐ k Y •
          chartSubmodule B S hS X.1 X.2 (⊤ : 𝒢.Submodule) Y
      downward_closed := by
        intro Y Y' f hf g
        rw [chartRestrictLinear_comp 𝒢 f g x]
        exact chartRestrictLinear_mem_chartIdealPow_smul B S hS X.1 X.2 ℐ k
          (⊤ : 𝒢.Submodule) g hf }
  exact mem_idealPowSmul_of_sieve B S hS X.1 X.2 ℐ k (⊤ : 𝒢.Submodule)
    (SmallEtale.mem_topology_openChartOfComparison_of_forall_affineOpens B S hS X A R h)
    fun _ _ hf => hf

section Factor

variable (I : IdealSheaves B S hS X.1 X.2)
  (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
  (G : Modules.{u, u} B S hS X.1 X.2)

/-- **A section of the chart restriction of `𝒢` over a Zariski open of the chart's scheme lying in
`Iᵏ` times that chart restriction is a section of the chart restriction of `ℐᵏ𝒢`.**  This is the
inclusion which `AlgebraicGeometry.Space.chartPushι_app_mem` lacks, and the two together make
`AlgebraicGeometry.Space.chartPushFactor` an isomorphism.

The scheme-side `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` is built from affine-local
data, so membership over `V` is tested on the affine opens inside it; there the semilinear
transport `AlgebraicGeometry.Space.mem_pow_chartSectionIdeal_smul_top_of_mem_pow_ideal_smul_top`
carries the honest product to the honest product of the ideal of sections of `ℐ` with the
sections of `𝒢` over the étale chart, which lies in the objectwise product; and the covering
sieve of the chart cut out by `V` glues those back together.

Only quasi-coherence of `𝒢` is carried, and only because the scheme-side product needs it to
exist: no affineness and no quasi-coherence of `ℐ` enters, the hard half of the affine-chart
description of `ℐᵏ𝒢` being needed for the other inclusion only. -/
theorem mem_chartSubmodule_idealPowSubmodule_of_mem_idealPowerMultiple
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ)
    {V : (chartScheme A).Opens} (y : Γ(chartPush B S hS X G A, V))
    (hy : y ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (idealSheafDataOfChart B S hS X I hIc A) k
        (chartPush B S hS X G A)).toSubmodule.obj (op V)) :
    (chartPushEquiv B S hS X G A V).toAddEquiv y
      ∈ chartSubmodule B S hS X.1 X.2 (idealPowSubmodule I k G)
          (openChartOfComparison B S hS X A V) := by
  have _hqc := isQuasicoherent_chartPush B S hS X G hGq A
  have hy' : y ∈ (Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul
      (idealSheafDataOfChart B S hS X I hIc A) k
        (chartPush B S hS X G A)).toSubmodule.obj (op V) :=
    (congrArg (fun P : (chartPush B S hS X G A).Submodule => y ∈ P.toSubmodule.obj (op V))
      (Stacks.AlgebraicGeometry.IdealPowerComparison.idealPowerMultiple_eq_idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A))).mp hy
  have haff := (Stacks.AlgebraicGeometry.IdealPowerSmul.mem_obj_idealPowSmul_iff
    (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) y).1 hy'
  refine mem_chartSubmodule_idealPowSubmodule_of_forall_affineOpens B S hS X I G k A _
    fun W hW => ?_
  have hrfl : chartRestrictLinear G (openChartOfComparisonHom B S hS X A hW)
        ((chartPushEquiv B S hS X G A V).toAddEquiv y)
      = (chartPushEquiv B S hS X G A W.1).toAddEquiv
          ((chartPush B S hS X G A).presheaf.map (homOfLE hW).op y) := rfl
  rw [hrfl]
  refine pow_chartSectionIdeal_smul_top_le_chartIdealPow_smul B S hS X.1 X.2 I G k
    (openChartOfComparison B S hS X A W.1) ?_
  exact mem_pow_chartSectionIdeal_smul_top_of_mem_pow_ideal_smul_top B S hS X.1 X.2 I G k
    (chartPush B S hS X G A) (openChartOfComparison B S hS X A W.1)
    (chartSectionsRingHom B S hS X A W.1)
    (chartPushEquiv B S hS X G A W.1).toAddEquiv.toAddMonoidHom
    (fun r z => chartPushEquiv_smul B S hS X G A W.1 r z)
    ((idealSheafDataOfChart B S hS X I hIc A).ideal W)
    (map_chartSectionsRingHom_openChartIdeal B S hS X I A W.1) (haff W hW)

/-! ### The factorization is an isomorphism -/

/-- **The component of `AlgebraicGeometry.Space.chartPushFactor` over a Zariski open of the
chart's scheme is bijective.**  It is the codomain restriction of the component of the chart
restriction of `ℐᵏ𝒢 ⟶ 𝒢`, which is the inclusion of a submodule; injectivity is therefore
formal, and surjectivity is
`AlgebraicGeometry.Space.mem_chartSubmodule_idealPowSubmodule_of_mem_idealPowerMultiple`. -/
theorem bijective_chartPushFactor_val_app
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (k : ℕ) (Y : ((chartScheme A).Opens)ᵒᵖ) :
    Function.Bijective ((chartPushFactor B S hS X I hIc G hIq hGq A k).val.app Y) := by
  obtain ⟨V⟩ := Y
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have h1 := congrArg (fun z => ((Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
        (idealSheafDataOfChart B S hS X I hIc A) k
          (chartPush B S hS X G A)).ι.val.app (op V)).hom z) hab
    exact Subtype.ext h1
  · refine ⟨(chartPushEquiv B S hS X (idealPowModule I k G) A V).symm
      ⟨(chartPushEquiv B S hS X G A V).toAddEquiv y.1,
        mem_chartSubmodule_idealPowSubmodule_of_mem_idealPowerMultiple B S hS X I hIc G hGq A k
          y.1 y.2⟩, ?_⟩
    exact Subtype.ext rfl

/-- **`AlgebraicGeometry.Space.chartPushFactor` is an isomorphism**: the chart restriction of
`ℐᵏ𝒢` *is* `Iᵏ` times the chart restriction of `𝒢`, not merely contained in it.

This is what Step 3 of [Stacks, Tag 07UM] needs: with it the direct system
`k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` is identified with the direct system of the first display of
[Stacks, Tag 01YB] on the chart's scheme, so the injectivity clause of that display becomes
usable on a chart. -/
theorem isIso_chartPushFactor (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ) :
    IsIso (chartPushFactor B S hS X I hIc G hIq hGq A k) :=
  Stacks.SheafOfModules.isIso_of_bijective_val_app _
    (bijective_chartPushFactor_val_app B S hS X I hIc G hIq hGq A k)

/-- **The chart restriction of `ℐᵏ𝒢` is `Iᵏ` times the chart restriction of `𝒢`**, as an
isomorphism of modules on the chart's scheme.  Its forward direction is
`AlgebraicGeometry.Space.chartPushFactor`. -/
def chartPushFactorIso (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ) :
    chartPush B S hS X (idealPowModule I k G) A ≅
      Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) :=
  @asIso _ _ _ _ (chartPushFactor B S hS X I hIc G hIq hGq A k)
    (isIso_chartPushFactor B S hS X I hIc G hIq hGq A k)

/-- The isomorphism of
`AlgebraicGeometry.Space.chartPushFactorIso` is `AlgebraicGeometry.Space.chartPushFactor`. -/
theorem chartPushFactorIso_hom (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ) :
    (chartPushFactorIso B S hS X I hIc G hIq hGq A k).hom
      = chartPushFactor B S hS X I hIc G hIq hGq A k := rfl

end Factor

end Sieves

end AlgebraicGeometry.Space

end
