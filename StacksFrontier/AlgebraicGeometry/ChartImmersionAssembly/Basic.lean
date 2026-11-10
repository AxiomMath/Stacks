module

public import StacksFrontier.AlgebraicGeometry.AmpleChartsOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectivityLabelChoice.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts

/-!
# Step 4 of Stacks Tag 01VS: the chart assembly on the source side

Step 4 of the proof of [Stacks, Tag 01VS] reads: *comparing coordinates, `j⁻¹(D₊(Tᵢ)) = X_{aᵢ}`
and `j` is a closed immersion into an affine open on each chart, hence an immersion.* This file
performs the passage from chart-local immersions to `AlgebraicGeometry.IsImmersion`, which is the
last of the conditions that `Stacks.AmpleImmersionReduction.ChartImmersion` requires, and supplies
the one-chart case at the hypothesis step 2 actually produces — *algebra* generators rather than
module generators.

## What is assembled, and out of what

Three results of the library:

* `Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict`: a morphism is an
  immersion as soon as it is one over a family of opens covering only its **range**. This is
  `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`.
* `Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`: `Proj R[T₀, …, Tₙ] ≅ ℙⁿ_R`, the
  chart identification.
* `Stacks.FiniteMorphismProjective.chartImmersion` with
  `Stacks.FiniteMorphismProjective.awayEval`: the morphism
  `Spec A ⟶ Proj R[T₀, …, Tₙ]` through the standard chart, and the ring homomorphism it is `Spec`
  of.

## The objection that the glue is "target-local only", and why it fails

`Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict` takes a family of opens of the
*target*, so it looks unusable for a cover of `X` by the charts `X_{sᵢ}`. It is usable, and
`Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_restrict_of_cover` is the statement that
says so: a family of opens of the **source** covering `X`, each landing inside a member of a
family of opens of the target, *is* a family of opens of the target covering the range, because
the range of `p` is the image of `X = ⨆ i, U i`. The hypothesis
`Set.range p ⊆ ⨆ i, W i` is implied, and nothing more about the target family is needed — in
particular the `W i` are not required to cover the target, which is exactly the case for the
standard charts of `ℙⁿ_S` cut down over affine opens of `S`.

Two separate facts make the passage work, and only the second is specific to the chart route:

* the standard charts of `ℙⁿ_S` cover `ℙⁿ_S` outright over **any** base — the integral charts
  cover the integral model and `ℙⁿ_S` maps to it, so
  `Stacks.ChartImmersionAssembly.iSup_standardOpen_eq_top` needs no base hypothesis and the glue
  could be run through `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` alone;
* the **refined** family, the `i`-th chart cut down over the affine open `Vᵢ` of `S` that
  `X_{sᵢ}` maps into, does *not* cover `ℙⁿ_S`, and that is where the range form is needed.
  `Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_chartOverRestrict` is the assembly at
  that family.

## Two docstrings in this tree assert a gap that is closed

The module docstrings of `StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison` and
`StacksFrontier.AlgebraicGeometry.ProjectivityLabelChoice.Basic` both say that invertibility of
`Stacks.AlgebraicGeometry.ProjPolyChart.projCompare` is unproved, the second giving that as the
reason the chart route is blocked. It is proved:
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` is a public instance, and
`Stacks.ChartImmersionAssembly.isImmersion_chartImmersion_projCompare` below consumes it.

## Main definitions

* `Stacks.ChartImmersionAssembly.chartOpenOver`: the `i`-th standard chart of `ℙⁿ_S`
  (`standardOpen`) cut down over an open of `S`.

## Main results

* `Stacks.ChartImmersionAssembly.iSup_standardOpen_eq_top`: **the standard charts cover `ℙⁿ_S`**.
* `Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_restrict_of_cover`: **a cover of the
  source suffices for the target-local glue** — the refutation of the objection above.
* `Stacks.ChartImmersionAssembly.nvCover_le_preimage_chartOpen`: **`X_{sᵢ}` lies in the preimage of
  the `i`-th chart**, for the pinned morphism of a family of sections. This is the half of step 4's
  `j⁻¹(D₊(Tᵢ)) = X_{aᵢ}` that the assembly uses, and it holds because `sᵢ/sᵢ = 1`.
* `Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_chartRestrict` and
  `Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_chartOverRestrict`: **the assembly**,
  at the full charts and at the charts refined over the base.
* `Stacks.ChartImmersionAssembly.chartEval_surjective_of_adjoin`,
  `Stacks.ChartImmersionAssembly.isImmersion_chartImmersion_of_adjoin`: **the one-chart case at
  algebra generators.** `Stacks.FiniteMorphismProjective.isImmersion_chartImmersion` asks for a
  family spanning `A` as an `R`-*module*, which is what Tag 0B3I's finite morphism supplies;
  step 2 of Tag 01VS supplies algebra generators instead, by [Stacks, Tag 01T2], and that is the
  hypothesis here.
* `Stacks.ChartImmersionAssembly.isImmersion_chartImmersion_projCompare` and
  `Stacks.ChartImmersionAssembly.chartImmersion_projCompare_fst`: the one-chart immersion
  transported to `ℙⁿ_{Spec R}` along the chart identification, over `Spec R`.

## What is not done

**No Stacks attribute is claimed, and in particular not tag 01VS.** Nothing here proves
`Stacks.AmpleImmersionReduction.ChartImmersion`: what the assembly still consumes is the
chart-local immersion hypothesis `∀ i, IsImmersion (p ∣_ chartOpenOver n S i (V i))`, and
producing it is [Stacks, Tag 01PW] together with the equalisation of the degrees of the numerators
it returns against the degree of the covering family. In particular no statement below mentions
ampleness, a tensor power or a degree.

The chart-local hypothesis is not yet connected to the one-chart case of the last section: that
connection needs the restriction `p ∣_ chartOpenOver n S i (V i)` identified with `Spec` of the
ring map `𝒪_S(Vᵢ)[T/Tᵢ] → 𝒪_X(X_{sᵢ})`, for which the handle is
`Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse` — the restriction of the
pinned morphism to the `i`-th chart is Mathlib's
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, built directly from a ring homomorphism.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveFromSections
open Stacks.SectionsToProjectiveSpace

namespace Stacks.ChartImmersionAssembly

open _root_.AlgebraicGeometry.ProjectiveSpace (standardOpen iSup_standardOpen_eq_top)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The standard charts of `ℙⁿ_S` over an arbitrary base -/

variable (n : ℕ) (S : Scheme.{u})

/-- Over an affine base the standard chart is the open the comparison of the two models of
projective space is proved local over. -/
theorem chartOpen_eq_baseChangeOpen (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    standardOpen n (Spec (CommRingCat.of R)) i =
      Stacks.AlgebraicGeometry.ProjBaseChange.baseChangeOpen R n i :=
  rfl

/-- **The `i`-th standard chart of `ℙⁿ_S` cut down over an open `V` of `S`.** This is the family
step 4 of [Stacks, Tag 01VS] uses, and unlike
`standardOpen` it does **not** cover `ℙⁿ_S`. -/
def chartOpenOver (i : Fin (n + 1)) (V : S.Opens) : (projectiveSpaceOver n S).Opens :=
  standardOpen n S i ⊓
    pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) ⁻¹ᵁ V

/-! ### A cover of the source gives a cover of the range -/

/-- **A family of opens of the source covering it, each landing in a member of a family of opens of
the target, makes that target family cover the range.** The range of `p` is the image of
`⨆ i, U i = ⊤`.

This is the step the "target-local only" objection to
`Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict` overlooks. -/
theorem range_subset_iSup_of_le_preimage {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type*}
    (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤) (W : ι → Y.Opens)
    (hle : ∀ i, U i ≤ p ⁻¹ᵁ W i) : Set.range p.base ⊆ (⨆ i, W i : Y.Opens) := by
  rintro - ⟨x, rfl⟩
  have hx : x ∈ (⨆ i, U i) := hU ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hle i hi⟩

/-- **A morphism is an immersion as soon as it is one over a family of opens of the target that a
cover of the source lands in.** The target family is not required to cover the target.

This is `Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict` fed by
`Stacks.ChartImmersionAssembly.range_subset_iSup_of_le_preimage`, and it is the shape the chart
route of [Stacks, Tag 01VS] wants: the source cover is the cover by the charts `X_{sᵢ}` and the
target family is the standard charts of `ℙⁿ_S` cut down over affine opens of `S`. -/
theorem isImmersion_of_isImmersion_restrict_of_cover {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type*}
    (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤) (W : ι → Y.Opens)
    (hle : ∀ i, U i ≤ p ⁻¹ᵁ W i) (himm : ∀ i, IsImmersion (p ∣_ W i)) : IsImmersion p :=
  IsZariskiLocalAtTarget.of_range_subset_iSup W (range_subset_iSup_of_le_preimage p U hU W hle) himm

/-! ### The charts of the source are the preimages of the charts of `ℙⁿ_S` -/

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The chart `X_{sᵢ}` lies in the preimage of the `i`-th standard chart of `ℙⁿ_S`**, for a
morphism `p` pinned on that chart by the ratio family of a family `s` of global sections of an
invertible `L`.

This is the inclusion half of step 4's `j⁻¹(D₊(Tᵢ)) = X_{aᵢ}`, and it is the half the assembly
needs. It holds for the cheapest possible reason: on `X_{sᵢ}` the `i`-th ratio is
`sᵢ/sᵢ = 1` (`Stacks.ProjectiveFromSections.chartRatio_self`), whose nonvanishing open is
everything. -/
theorem nvCover_le_preimage_chartOpen {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    nvCover s i ≤ p ⁻¹ᵁ standardOpen n S i := by
  have h2 : toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) = ⊤ := by
    rw [preimage_basicOpen, chartRatio_self, Scheme.basicOpen_one]
  have key : (nvCover s i).ι ⁻¹ᵁ (p ⁻¹ᵁ standardOpen n S i) = ⊤ :=
    (congrArg (fun q : (nvCover s i).toScheme ⟶ projectiveSpaceAtUniverse.{u} n =>
      q ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)) hchart).trans h2
  intro x hx
  have hr : x ∈ Set.range (nvCover s i).ι.base := by
    rw [Scheme.Opens.range_ι]; exact hx
  obtain ⟨y, hy⟩ := hr
  have hy' : y ∈ (nvCover s i).ι ⁻¹ᵁ (p ⁻¹ᵁ standardOpen n S i) := key ▸ trivial
  rw [← hy]
  exact hy'

/-! ### The assembly -/

/-- **Step 4 of [Stacks, Tag 01VS] at the full charts of `ℙⁿ_S`.** A morphism to `ℙⁿ_S` that is an
immersion over each standard chart is an immersion, over any base scheme.

This is `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` at
`Stacks.ChartImmersionAssembly.iSup_standardOpen_eq_top`; the range form of the glue is not needed
here, because the full charts do cover `ℙⁿ_S`. -/
theorem isImmersion_of_isImmersion_chartRestrict {n : ℕ} {S : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) (himm : ∀ i, IsImmersion (p ∣_ standardOpen n S i)) :
    IsImmersion p :=
  IsZariskiLocalAtTarget.of_iSup_eq_top _ (iSup_standardOpen_eq_top n S) himm

/-- **Step 4 of [Stacks, Tag 01VS], at the family the source's argument uses.**

`p` is the morphism to `ℙⁿ_S` over `S` pinned on each chart `X_{sᵢ}` by the ratio family of a
generating family `s` of global sections of an invertible `L`, and `Vᵢ` is an affine open of `S`
that `X_{sᵢ}` maps into. If `p` is an immersion over each `D₊(Tᵢ) ∩ pr⁻¹(Vᵢ)` then `p` is an
immersion.

The family of opens of `ℙⁿ_S` here covers only the range of `p`, which is what
`Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_restrict_of_cover` asks for. Every
hypothesis other than the chart-local immersion is supplied by
`Stacks.AmpleChartsOverBase.exists_generating_hom_over_of_isAmple` from ampleness alone. -/
theorem isImmersion_of_isImmersion_chartOverRestrict {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) {S : Scheme.{u}} {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (hchart : ∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : Fin (n + 1) → S.Opens) (hV : ∀ i, nvCover s i ≤ f ⁻¹ᵁ V i)
    (himm : ∀ i, IsImmersion (p ∣_ chartOpenOver n S i (V i))) :
    IsImmersion p := by
  refine isImmersion_of_isImmersion_restrict_of_cover p (nvCover s)
    (isOpenCover_nvCover_of_generatesStalks s hs) _ (fun i => ?_) himm
  rw [chartOpenOver, Scheme.Hom.preimage_inf]
  refine le_inf (nvCover_le_preimage_chartOpen s p i (hchart i)) ?_
  rw [← Scheme.Hom.comp_preimage, hpf]
  exact hV i

/-! ### The one-chart case at algebra generators -/

section OneChart

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (m : ℕ)
  (a : {j : Fin (m + 1) // j ≠ 0} → A)

/-- **The evaluation `R[Y_j : j ≠ 0] → A` is surjective as soon as the family generates `A` as an
`R`-algebra.** `Stacks.FiniteMorphismProjective.chartEval_surjective` asks for the family to
span `A` as an `R`-*module*, which is what the finite morphism of [Stacks, Tag 0B3I] supplies;
step 2 of [Stacks, Tag 01VS] supplies algebra generators instead, by [Stacks, Tag 01T2]. -/
theorem chartEval_surjective_of_adjoin (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    Function.Surjective (Stacks.FiniteMorphismProjective.chartEval R A m a) := by
  intro x
  have hx : x ∈ Algebra.adjoin R (Set.range a) := hgen ▸ Algebra.mem_top
  rw [Algebra.adjoin_range_eq_range_aeval] at hx
  obtain ⟨q, hq⟩ := (AlgHom.mem_range _).mp hx
  exact ⟨q, by simpa [Stacks.FiniteMorphismProjective.chartEval, MvPolynomial.aeval_def] using hq⟩

/-- **A finite type algebra is a quotient of the standard affine chart `R[T]_{(T₀)}`.** The
algebra-generation form of `Stacks.FiniteMorphismProjective.awayEval_surjective`. -/
theorem awayEval_surjective_of_adjoin (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    Function.Surjective (Stacks.FiniteMorphismProjective.awayEval R A m a) :=
  (chartEval_surjective_of_adjoin R A m a hgen).comp (chartEquiv R m 0).symm.surjective

/-- **The chart morphism `Spec A ⟶ Proj R[T₀, …, Tₘ]` is an immersion when the family generates
`A` as an `R`-algebra**: a closed immersion into the standard affine chart followed by the open
immersion of that chart. The algebra-generation form of
`Stacks.FiniteMorphismProjective.isImmersion_chartImmersion`. -/
theorem isImmersion_chartImmersion_of_adjoin (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    IsImmersion (Stacks.FiniteMorphismProjective.chartImmersion R A m a) := by
  have hcl : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Stacks.FiniteMorphismProjective.awayEval R A m a))) :=
    IsClosedImmersion.spec_of_surjective _ (awayEval_surjective_of_adjoin R A m a hgen)
  have himm : IsImmersion
      (Spec.map (CommRingCat.ofHom (Stacks.FiniteMorphismProjective.awayEval R A m a)) ≫
      AlgebraicGeometry.Proj.awayι (polyGrading R m) (MvPolynomial.X 0) (X_mem_one R m 0)
        Nat.one_pos) := inferInstance
  exact himm

/-- **The one-chart immersion, transported to `ℙⁿ_{Spec R}` along the chart identification.**

This is where `Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` is consumed: the
comparison `Proj R[T₀, …, Tₘ] ⟶ ℙᵐ_{Spec R}` is an isomorphism, hence an immersion, and immersions
compose. -/
theorem isImmersion_chartImmersion_projCompare (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    IsImmersion (Stacks.FiniteMorphismProjective.chartImmersion R A m a ≫ projCompare R m) := by
  have := isImmersion_chartImmersion_of_adjoin R A m a hgen
  infer_instance

/-- **The one-chart immersion lies over `Spec R`**: composed with the structure morphism of
`ℙᵐ_{Spec R}` it is `Spec` of the structure map of the algebra. No hypothesis on the family is
needed. -/
theorem chartImmersion_projCompare_fst :
    (Stacks.FiniteMorphismProjective.chartImmersion R A m a ≫ projCompare R m) ≫
        pullback.fst (terminal.from (Spec (CommRingCat.of R)))
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [Category.assoc, projCompare_fst,
    Stacks.FiniteMorphismProjective.chartImmersion_projToSpecCoeff]

end OneChart

end Stacks.ChartImmersionAssembly

end
