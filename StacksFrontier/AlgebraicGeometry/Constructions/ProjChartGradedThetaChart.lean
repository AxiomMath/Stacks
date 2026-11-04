module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerSemilinear

/-!
# The chart datum of `θ` for Stacks Tag 01NK: the scalars

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map, and let `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜` be the morphism
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`. The comparison

  `θ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`

of [Stacks, Tag 01NK] is built from its adjoint transpose, a family of morphisms
`𝒪_X(n) ⟶ (r_{L, ψ})_* (L^{⊗ n}|_{U(ψ)})` of sheaves of `𝒪_{Proj 𝒜}`-modules. Those are glued
from data on the standard opens `D₊(f)`, and on `D₊(f)` the datum is a map of modules over the
chart's coordinate ring `A_{(f)}`. **This file supplies the scalars of that chart datum**: it
identifies the action of `r_{L, ψ}` on the functions on `D₊(f)` with the dehomogenisation ring map
`A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` that the chart of `f` was built from. That identification is what
makes the chart comparison of
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` — which is
`A_{(f)}`-semilinear along exactly that ring map — a morphism of `A_{(f)}`-modules into the
sections of the direct image.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.laurentPiece` and
  `…GradedSections.pushLaurent` — `L^{⊗ n}|_{U(ψ)}` and its direct image
  `(r_{L, ψ})_* (L^{⊗ n}|_{U(ψ)})`, **the target of the degree-`n` component of `θ` in its
  pushforward form**.
* `…GradedSections.chartOpen` — the image in `T` of `r_{L, ψ}^{-1}(D₊(f))`, which clause (1) of
  the tag identifies with `T_{ψ(f)}` (`…GradedSections.chartOpen_eq`).
* `…GradedSections.chartTargetIso` — **the sections of the direct image over `D₊(f)` are the
  sections of `L^{⊗ n}` over the chart open.**

## Main results

* `Stacks.MorphismToProj.HomogeneousRatios.awayToSection_chartToProj_appLE` — **a chart morphism
  built from a family of homogeneous ratios acts on the functions on `D₊(f)` by the ring map it
  was built from.**
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_le` — `r_{L, ψ}`
  restricted to any open inside `T_{ψ(f)}` is the chart of `f` over that open.
* `…GradedSections.awayToSection_glued_app` — **`r_{L, ψ}` acts on the functions on `D₊(f)` by the
  dehomogenisation ring map of `f`.** This is the scalar compatibility the chart datum of `θ`
  needs.

## Implementation notes

`chartOpen` is an `abbrev`, not a `def`. Its body is the open on which the target sections are
actually indexed, and the comparison `chartTargetIso` is the identification of restricted
sections with sections over an image at the *tautological* presentation of that image — so it
carries no `eqToHom` and the clause (1) equality `chartOpen_eq` is never transported along. Were
`chartOpen` semireducible the two spellings would not unify at reducible transparency and a goal
mixing them would not be type-correct, which is the failure mode the ascribed `have` at the end of
`awayToSection_glued_app` works around for the one step where both occur.

The three `appLE` lemmas the proofs run on —
`Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE`,
`…ProjChartSections.appLE_top_top` and `…ProjChartSections.appLE_congr_hom` — are proved in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart`; the last is what transports an
`appLE` along an equality of morphisms, which cannot be done by rewriting because the inequality
of opens that `appLE` carries mentions the morphism.

The container type `σ` of the grading lives in an arbitrary universe, independent of that of
the ring, as in `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_mul`
and `Stacks.AlgebraicGeometry.ProjChartSections`.

## No tag is claimed

`θ` itself is not built here, so no `stacks` attribute is attached: what this file proves is the
scalar bookkeeping of one chart, not a clause of the tag.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousLocalization
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.AlgebraicGeometry.ProjChartSections
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (imageSectionsIso imageSectionsIso_smul)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

universe u w

namespace Stacks.MorphismToProj.HomogeneousRatios

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {f : A} {hf : f ∈ 𝒜 d}
  {X : Scheme.{u}} {U : X.Opens}

/-- **The chart morphism acts on the sections of `𝒪_{Proj 𝒜}` over `D₊(f)` by the ring map it was
built from.** Read through `AlgebraicGeometry.Proj.awayToSection`, which identifies `A_{(f)}` with
those sections, and through `AlgebraicGeometry.Scheme.Opens.topIso`, which identifies
`Γ(U.toScheme, ⊤)` with `Γ(X, U)`, the map `Scheme.Hom.appLE` of `chartToProj` is `lift`. -/
theorem awayToSection_chartToProj_appLE
    (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d)
    (hpre : (⊤ : U.toScheme.Opens)
      ≤ R.chartToProj hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        (R.chartToProj hd).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hpre
      = CommRingCat.ofHom (R.lift hd) ≫ U.topIso.inv := by
  have e₁ : (⊤ : (Spec (CommRingCat.of (Away 𝒜 f))).Opens)
      ≤ AlgebraicGeometry.Proj.awayι 𝒜 f hf hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
    (awayι_preimage_basicOpen_self 𝒜 hf hd).ge
  have e₂ : (⊤ : U.toScheme.Opens) ≤ R.toSpecAway hd ⁻¹ᵁ ⊤ := by simp
  have hc : (R.chartToProj hd).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hpre
      = (R.toSpecAway hd ≫ AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).appLE
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤
          (e₂.trans ((Opens.map (R.toSpecAway hd).base).map (homOfLE e₁)).le) :=
    appLE_congr_hom rfl _ _ _ _
  have hsplit : (R.toSpecAway hd ≫ AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).appLE
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤
        (e₂.trans ((Opens.map (R.toSpecAway hd).base).map (homOfLE e₁)).le)
      = (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).appLE
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ e₁ ≫
        (R.toSpecAway hd).appLE ⊤ ⊤ e₂ :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₁ e₂).symm
  rw [hc, hsplit, ← Category.assoc, awayToSection_comp_awayι_appLE 𝒜 hf hd,
    appLE_top_top _ e₂]
  exact R.toSpecAway_appTop hd

end Stacks.MorphismToProj.HomogeneousRatios

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {e : ℕ} {f : A}

/-- **`r_{L, ψ}` restricted to any open inside `T_{ψ(f)}` is the chart of `f` over that open.**
This is `homOfLE_glued_of_pos` followed by the compatibility `homOfLE_chartToProj` of the chart
with restriction. -/
theorem GradedSections.homOfLE_glued_le (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
    (h : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩)) :
    T.homOfLE (h.trans (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he)) ≫ ψ.glued
      = ψ.chartToProj hf h he := by
  rw [show T.homOfLE (h.trans (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he))
      = T.homOfLE h ≫ T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he) from
    (Scheme.homOfLE_homOfLE T h _).symm, Category.assoc,
    ψ.homOfLE_glued_of_pos hf he, ψ.homOfLE_chartToProj hf le_rfl he h]

/-- `L^{⊗ n}` restricted to the open `U(ψ)`. -/
def GradedSections.laurentPiece (n : ℤ) : ψ.coveringOpen.toScheme.Modules :=
  (tensorPowerModule T L n).restrict ψ.coveringOpen.ι

/-- **The direct image `(r_{L, ψ})_* (L^{⊗ n}|_{U(ψ)})` on `Proj 𝒜`**, the target of the degree-`n`
component of `θ` in its pushforward form. -/
def GradedSections.pushLaurent (n : ℤ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  (Scheme.Modules.pushforward ψ.glued).obj (ψ.laurentPiece n)

/-- **The chart open**: the image in `T` of the preimage of `D₊(f)` under `r_{L, ψ}`. By clause
(1) of the tag it is `T_{ψ(f)}`, but it is this spelling that makes the comparison of sections
below need no transport. -/
abbrev GradedSections.chartOpen (f : A) : T.Opens :=
  ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)

/-- **Clause (1) of [Stacks, Tag 01NK] in the `chartOpen` spelling.** -/
theorem GradedSections.chartOpen_eq (hf : f ∈ 𝒜 e) (he : 0 < e) :
    ψ.chartOpen f = nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) :=
  ψ.image_preimage_basicOpen_glued hf he

/-- **The sections of the direct image over `D₊(f)` are the sections of `L^{⊗ n}` over the chart
open.** The sections of a pushforward over `D₊(f)` *are* the sections over the preimage, by `rfl`,
and the sections of a restriction over an open *are* the sections over its image, so with
`chartOpen` defined as that image the comparison carries no `eqToHom`. -/
def GradedSections.chartTargetIso (n : ℤ) (f : A) :
    Γ(ψ.pushLaurent n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      ≅ Γ(tensorPowerModule T L n, ψ.chartOpen f) :=
  imageSectionsIso ψ.coveringOpen.ι (tensorPowerModule T L n)
    (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) (ψ.chartOpen f) rfl

/-- **`r_{L, ψ}` acts on the functions on `D₊(f)` by the dehomogenisation ring map of `f`.**
Read through `AlgebraicGeometry.Proj.awayToSection` on the source and through the identification
of the sections of `U(ψ)` over the preimage with the sections of `T` over the chart open on the
target, the action of `r_{L, ψ}` on `Γ(Proj 𝒜, D₊(f))` is
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homogeneousRatios`'s `lift`. -/
theorem GradedSections.awayToSection_glued_app (hf : f ∈ 𝒜 e) (he : 0 < e) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        ψ.glued.app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ≫
        (ψ.coveringOpen.ι.appIso
          (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)).inv
      = CommRingCat.ofHom
          ((ψ.homogeneousRatios hf (ψ.chartOpen_eq hf he).le).lift he) := by
  set W := ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f with hW
  have hV : ψ.chartOpen f
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) :=
    (ψ.chartOpen_eq hf he).le
  have hVU : ψ.chartOpen f ≤ ψ.coveringOpen :=
    hV.trans (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he)
  have hg : T.homOfLE hVU ≫ ψ.glued = ψ.chartToProj hf hV he :=
    ψ.homOfLE_glued_le hf he hV
  have hpre : (⊤ : (ψ.chartOpen f).toScheme.Opens)
      ≤ ψ.chartToProj hf hV he ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
    fun x _ => (ψ.homogeneousRatios hf hV).chartToProj_base_mem he x
  have e' : (⊤ : (ψ.chartOpen f).toScheme.Opens) ≤ T.homOfLE hVU ⁻¹ᵁ W := by
    rw [hW, ← Scheme.Hom.comp_preimage, hg]
    exact hpre
  -- the identification of restricted sections, read as an `appLE`
  have hiso : (ψ.coveringOpen.ι.appIso W).hom ≫ (T.homOfLE hVU).appLE W ⊤ e'
      = (ψ.chartOpen f).topIso.inv := by
    have h1 : (ψ.coveringOpen.ι.appIso W).hom
        = ψ.coveringOpen.ι.appLE (ψ.coveringOpen.ι ''ᵁ W) W
            (Scheme.Hom.preimage_image_eq ψ.coveringOpen.ι W).ge :=
      Scheme.Hom.appIso_hom' _ _
    rw [h1, Scheme.Hom.appLE_comp_appLE]
    exact (appLE_congr_hom (T.homOfLE_ι hVU) _ _ _ _).trans
      (ι_appLE_top (ψ.chartOpen f))
  have hgiso : (T.homOfLE hVU).appLE W ⊤ e'
      = (ψ.coveringOpen.ι.appIso W).inv ≫ (ψ.chartOpen f).topIso.inv :=
    (Iso.eq_inv_comp _).mpr hiso
  -- the chart identity, transported along `hg`
  have hmain : AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
      (ψ.glued.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W le_rfl ≫
        (T.homOfLE hVU).appLE W ⊤ e')
      = CommRingCat.ofHom ((ψ.homogeneousRatios hf hV).lift he) ≫
          (ψ.chartOpen f).topIso.inv := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hg _ _ _ hpre]
    exact (ψ.homogeneousRatios hf hV).awayToSection_chartToProj_appLE he hpre
  rw [hgiso, Scheme.Hom.appLE_eq_app] at hmain
  -- the two spellings `ι ''ᵁ W` and `chartOpen f` of the chart open are the same term, but a
  -- goal mixing them is not type-correct at reducible transparency; the ascription below is
  -- checked at default transparency, where the bridge is `rfl`.
  have hfinal : (AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        ψ.glued.app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ≫
        (ψ.coveringOpen.ι.appIso
          (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)).inv) ≫
      (ψ.chartOpen f).topIso.inv
      = CommRingCat.ofHom
            ((ψ.homogeneousRatios hf (ψ.chartOpen_eq hf he).le).lift he) ≫
          (ψ.chartOpen f).topIso.inv := by
    rw [Category.assoc, Category.assoc]
    exact hmain
  exact (cancel_mono (ψ.chartOpen f).topIso.inv).mp hfinal

end Stacks.AlgebraicGeometry.ProjChartFullGraded

end
