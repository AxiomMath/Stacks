module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Chart
public import StacksFrontier.AlgebraicGeometry.SectionRingProjOverlap.Basic
public import StacksFrontier.AlgebraicGeometry.ProjAwayChartFactor.Basic

/-!
# The chart of `Proj Γ_*(X, L)` over an open inside `X_a`, and its basic opens

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a homogeneous element of degree
`d > 0` of the graded section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV.
`StacksFrontier/AlgebraicGeometry/SectionRingChartMap/Chart.lean` builds the chart morphism
`X_a ⟶ Proj Γ_*(X, L)` out of the ring map `Γ_*(X, L)₍a₎ ⟶ Γ(X, X_a)`, which
`Stacks.SectionRingChartMap.chartRingMap` provides over **any** open `V ≤ X_a`. Gluing the charts
over the cover `{X_a}` of Stacks Tag 01PZ needs them on the overlaps, so this file frees the open:
`Stacks.SectionRingChartOpen.chartHomOn` is the chart over an arbitrary `V ≤ X_a`, and at
`V = X_a` it is `Stacks.SectionRingChartMap.chartHom` on the nose.

Two things become statable once the open is free, and both are proved here: that the charts over
two nested opens agree, and **clause (1) of Stacks Tag 01PZ for a single chart** — the chart over
`V ≤ X_a` pulls the basic open `D₊(b)` of `Proj Γ_*(X, L)` back to `V ∩ X_b`, for `b` homogeneous
of any positive degree.

## Main definitions

* `Stacks.SectionRingChartOpen.chartHomOn`: **the chart over `V ≤ X_a`**, with the proof that it
  lands in `D₊(a)`. `Stacks.SectionRingChartOpen.chartHomOn_self` is the identification with
  `Stacks.SectionRingChartMap.chartHom` at `V = X_a`, by `rfl`.

## Main results

* `Stacks.SectionRingChartOpen.map_ratio`, `map_ratioR`, `map_chartRingMap`: **the ratio and the
  chart ring map are compatible with restriction.** The ratio is characterized by an identity
  between sections (`Stacks.SectionRingChartMap.ratio_unique`), and restriction carries that
  identity along; the chart ring map then follows on the fractions `x / aⁿ`, which generate.
* `Stacks.SectionRingChartOpen.chartHomOn_val`: **the chart factors through `Spec` of the
  degree-zero localization**, by
  `Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_symm_val`. Everything below runs on
  this: it is what brings Mathlib's `AlgebraicGeometry.Proj.awayι` into contact with the chart.
* `Stacks.SectionRingChartOpen.homOfLE_chartHomOn`: **the charts over two nested opens agree.**
* `Stacks.SectionRingChartOpen.chartHomOn_preimage_projBasicOpen`: **clause (1) of Stacks Tag
  01PZ for one chart**, `f ⁻¹ᵁ D₊(b) = V ∩ X_b`.
* `Stacks.SectionRingChartOpen.chartRingMap_isLocalizationElem` and `exists_numerator`: the two
  halves of that computation — the value of the chart ring map on Mathlib's
  `HomogeneousLocalization.Away.isLocalizationElem`, which is the fraction `bᵈ / aᵉ`, and the
  identification of the nonvanishing open of its numerator with `X_a ∩ X_b`.

## Implementation notes

**The geometric step is available and unconditional.**
`Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` says that if `t|_V = g · σ|_V` with
`σ` nowhere vanishing on `V`, then `X_t ∩ V` is the basic open of `g`. Applied to the defining
identity of `Stacks.SectionRingChartMap.ratio` it turns the basic open of a ratio back into a
nonvanishing open, which is exactly the shape clause (1) asks for. No affineness and no
quasi-compactness are used anywhere in this file.

**The one degree equation is crossed on ring elements, never on sections.** The numerator of the
fraction `bᵈ / aᵉ`, multiplied by `a` as the shifted family of
`StacksFrontier/AlgebraicGeometry/SectionRingChartMap/Chart.lean` requires, is `a · bᵈ`, a
homogeneous element of degree `d + e d`; the denominator `a^{e+1}` has degree
`d (e + 1)`. The two numbers are equal and not `rfl`-equal, and
`Stacks.SectionRingChartOpen.exists_numerator` produces the numerator *as a section of degree
`d (e + 1)`* by reading a membership `∈ grading L (d (e + 1))` off the ring equation — a rewrite
inside a proposition — rather than transporting a section. Its nonvanishing open is then compared
with that of `a · bᵈ` by `Stacks.SectionRingChartOpen.nvOpen_congr`, whose proof is a `subst` of
an equation between two variables.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)

## What is not done

**The glued morphism is not constructed here** and no `@[stacks]` attribute is attached: what is
proved is clause (1) for one chart. The agreement of the charts at *different* homogeneous
elements on their common overlap — the other half of the gluing — is the sibling file
`Overlap.lean`, and the gluing itself is
`StacksFrontier/AlgebraicGeometry/SectionRingProjMorphism/Basic.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)

universe u

namespace Stacks.SectionRingChartOpen

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

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### Two spellings of one degree -/

/-- **The nonvanishing open depends only on the ring element.** Two homogeneous sections of equal
— not necessarily identical — degree with the same image in `Γ_*(X, L)` have the same
nonvanishing open. The degree equation is eliminated by `subst` on two variables, exactly as in
`Stacks.SectionRingChartMap.ratioR_congr`, so the lemma applies at arbitrary compound degrees
with no transport. -/
public theorem nvOpen_congr {j j' : ℕ} (hjj : j = j') (s : powSections L j)
    (s' : powSections L j')
    (hss : DirectSum.of (powSections L) j s = DirectSum.of (powSections L) j' s') :
    nvOpen L s = nvOpen L s' := by
  subst hjj
  obtain rfl : s = s' := by
    have h := DirectSum.of_eq_same (β := fun i ↦ powSections L i) j s
    rw [hss, DirectSum.of_eq_same] at h
    exact h.symm
  rfl

/-! ### The ratio is compatible with restriction -/

variable {V V' : X.Opens}

/-- **Restricting a ratio restricts its numerator and denominator.** The ratio `s / g` computed on
`V` restricts, along an inclusion `V' ≤ V`, to the ratio `s / g` computed on `V'`. -/
public theorem map_ratio {j : ℕ} (g : powSections L j) (hV : V ≤ nvOpen L g)
    (hV' : V' ≤ nvOpen L g) (hle : V' ≤ V) (s : powSections L j) :
    X.presheaf.map (homOfLE hle).op (Stacks.SectionRingChartMap.ratio L g hV s)
      = Stacks.SectionRingChartMap.ratio L g hV' s := by
  refine (Stacks.SectionRingChartMap.ratio_unique L g hV' s _ ?_).symm
  rw [← Stacks.TensorPowerTrivialize.map_smul_resTop (natTensorPow L j) (globalSection X _ g)
      (homOfLE hle) (Stacks.SectionRingChartMap.ratio L g hV s),
    Stacks.SectionRingChartMap.ratio_smul_resTop L g hV s,
    Stacks.TensorPowerTrivialize.res_resTop (natTensorPow L j) (globalSection X _ s)
      (homOfLE hle)]

/-- `Stacks.SectionRingChartOpen.map_ratio` read on the section ring. -/
public theorem map_ratioR {j : ℕ} (g : powSections L j) (hV : V ≤ nvOpen L g)
    (hV' : V' ≤ nvOpen L g) (hle : V' ≤ V) (z : sectionRing L) :
    X.presheaf.map (homOfLE hle).op (Stacks.SectionRingChartMap.ratioR L g hV z)
      = Stacks.SectionRingChartMap.ratioR L g hV' z := by
  rw [Stacks.SectionRingChartMap.ratioR_apply, Stacks.SectionRingChartMap.ratioR_apply, map_ratio]

variable {d : ℕ} (a : powSections L d)

/-- `Stacks.SectionRingChartMap.chartRingMap_mk` with the degree of the denominator left free,
constrained only by an equation. Both freedoms are needed: the fractions
`HomogeneousLocalization.awayMap_mk` produces carry a different proof of homogeneity and present
the degree of a product as the sum of the two degrees rather than in whatever spelling the
denominator came in. The equation is eliminated by `subst` on a variable, so this applies at
arbitrary compound degrees with no transport. -/
public theorem chartRingMap_mk' {m : ℕ} (hV : V ≤ nvOpen L a) (hm : m = d)
    (ha : DirectSum.of (powSections L) d a ∈ grading L m) (n : ℕ) (x : sectionRing L)
    (hx : x ∈ grading L (n • m)) :
    Stacks.SectionRingChartMap.chartRingMap L a hV
        (HomogeneousLocalization.Away.mk (grading L) ha n x hx)
      = Stacks.SectionRingChartMap.chartFamily L a hV n x := by
  subst hm
  exact Stacks.SectionRingChartMap.chartRingMap_mk L a hV n x hx

/-- **The chart ring map is compatible with restriction.** Composing the chart ring map on `V`
with the restriction `Γ(X, V) ⟶ Γ(X, V')` gives the chart ring map on `V'`. -/
public theorem map_chartRingMap (hV : V ≤ nvOpen L a) (hV' : V' ≤ nvOpen L a) (hle : V' ≤ V)
    (x : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a)) :
    X.presheaf.map (homOfLE hle).op (Stacks.SectionRingChartMap.chartRingMap L a hV x)
      = Stacks.SectionRingChartMap.chartRingMap L a hV' x := by
  obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading L)
    (Stacks.ExternalGrading.of_mem_summand d a) x
  rw [Stacks.SectionRingChartMap.chartRingMap_mk, Stacks.SectionRingChartMap.chartRingMap_mk,
    Stacks.SectionRingChartMap.chartFamily_apply, Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.numMapR_def, Stacks.SectionRingChartMap.numMapR_def, map_ratioR]

/-! ### The chart over an arbitrary open inside `X_a` -/

/-- **The chart morphism over an open `V ≤ X_a`, with the proof that it lands in `D₊(a)`.** This
is `Stacks.SectionRingChartMap.chartHomSubtype` with the open freed from being `X_a` itself: at
`V = X_a` the two are the same term. -/
public noncomputable def chartHomOn (hd : 0 < d) (hV : V ≤ nvOpen L a) :
    {g : V.toScheme ⟶ Proj (grading L) //
      g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = ⊤} :=
  (Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) hd V.toScheme).symm
    (CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a hV) ≫
      (Scheme.Opens.topIso V).inv)

/-- **At `V = X_a` the chart over an open is the chart morphism
`Stacks.SectionRingChartMap.chartHom`.** -/
public theorem chartHomOn_self (hd : 0 < d) :
    (chartHomOn L a hd (le_refl (nvOpen L a))).1 = Stacks.SectionRingChartMap.chartHom L a hd :=
  rfl

/-- **The chart over `V` factors through `Spec` of the degree-zero localization at `a`.** This is
the shape in which Mathlib's knowledge of `AlgebraicGeometry.Proj.awayι` applies to it. -/
public theorem chartHomOn_val (hd : 0 < d) (hV : V ≤ nvOpen L a) :
    (chartHomOn L a hd hV).1
      = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a hV))
          ≫ Proj.awayι (grading L) (DirectSum.of (powSections L) d a)
            (Stacks.ExternalGrading.of_mem_summand d a) hd := by
  rw [chartHomOn, Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_symm_val,
    Spec.map_comp, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc]

/-- **The charts over two nested opens agree.** The chart over `V` restricted to `V' ≤ V` is the
chart over `V'`; this is `Stacks.SectionRingChartOpen.map_chartRingMap` read geometrically. -/
public theorem homOfLE_chartHomOn (hd : 0 < d) (hV : V ≤ nvOpen L a) (hV' : V' ≤ nvOpen L a)
    (hle : V' ≤ V) :
    X.homOfLE hle ≫ (chartHomOn L a hd hV).1 = (chartHomOn L a hd hV').1 := by
  have hring : CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a hV) ≫
      X.presheaf.map (homOfLE hle).op
        = CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a hV') :=
    CommRingCat.hom_ext (RingHom.ext fun x ↦ map_chartRingMap L a hV hV' hle x)
  rw [chartHomOn_val, chartHomOn_val, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map V' V hle, Category.assoc, ← Spec.map_comp_assoc,
    hring]

/-! ### The chart ring map on the localization element of a second homogeneous element -/

/-- **The value of the chart ring map at `a` on the element `bᵈ / aᵉ`.** For `b` homogeneous of
degree `e`, Mathlib's `HomogeneousLocalization.Away.isLocalizationElem` is the fraction
`bᵈ / aᵉ`, and `AlgebraicGeometry.Proj.awayι_preimage_basicOpen` says that the chart at `a` meets
`D₊(b)` exactly where that fraction is invertible. Its value under the chart ring map is the
geometric ratio of `a bᵈ` by `a^{e+1}`, and `s` names the numerator as a section. -/
public theorem chartRingMap_isLocalizationElem (hV : V ≤ nvOpen L a) {e : ℕ}
    (b : powSections L e) (s : powSections L (d * (e + 1)))
    (hs : DirectSum.of (powSections L) (d * (e + 1)) s
      = DirectSum.of (powSections L) d a * DirectSum.of (powSections L) e b ^ d) :
    Stacks.SectionRingChartMap.chartRingMap L a hV
        (HomogeneousLocalization.Away.isLocalizationElem
          (Stacks.ExternalGrading.of_mem_summand d a)
          (Stacks.ExternalGrading.of_mem_summand e b))
      = Stacks.SectionRingChartMap.ratio L (powSec L a (e + 1))
          (Stacks.SectionRingChartMap.le_nvOpen_powSec L a hV (e + 1) (Nat.le_add_left 1 e)) s := by
  rw [HomogeneousLocalization.Away.isLocalizationElem, chartRingMap_mk' L a hV rfl,
    Stacks.SectionRingChartMap.chartFamily_apply, Stacks.SectionRingChartMap.numMapR_def, ← hs,
    Stacks.SectionRingChartMap.ratioR_of]

/-- **The numerator of `a bᵈ` as a section of degree `d (e + 1)`.** The product
`a · bᵈ` is a homogeneous element of the section ring of degree `d + e d`, which is the degree
`d (e + 1)` of `a^{e+1}` written differently; this produces the section naming it in the spelling
the ratio by `a^{e+1}` consumes, together with the identification of its nonvanishing open. -/
public theorem exists_numerator (hd : 0 < d) {e : ℕ} (b : powSections L e) :
    ∃ s : powSections L (d * (e + 1)),
      DirectSum.of (powSections L) (d * (e + 1)) s
          = DirectSum.of (powSections L) d a * DirectSum.of (powSections L) e b ^ d ∧
        nvOpen L s = nvOpen L a ⊓ nvOpen L b := by
  have hprod : DirectSum.of (powSections L) (d + e * d) (mul a (powSec L b d))
      = DirectSum.of (powSections L) d a * DirectSum.of (powSections L) e b ^ d := by
    rw [Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow]
  have hdeg : d * (e + 1) = d + e * d := by ring
  have hmem : DirectSum.of (powSections L) d a * DirectSum.of (powSections L) e b ^ d
      ∈ grading L (d * (e + 1)) := by
    rw [← hprod, hdeg]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  obtain ⟨s, hs⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hmem
  refine ⟨s, hs, ?_⟩
  rw [nvOpen_congr L hdeg s (mul a (powSec L b d)) (hs.trans hprod.symm),
    Stacks.SectionRingChartMap.nvOpen_mul,
    Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L b d hd]

/-! ### The preimages of the basic opens of `Proj` under the chart -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- An open inside another has the whole of its own subscheme as the preimage of the larger. -/
private theorem ι_preimage_eq_top {W U : X.Opens} (h : W ≤ U) : W.ι ⁻¹ᵁ U = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ h x.2

/-- **Clause (1) of Stacks Tag 01PZ for a single chart.** The chart over an open `V ≤ X_a` pulls
the basic open `D₊(b)` of `Proj Γ_*(X, L)`, for `b` homogeneous of any positive degree, back to
`V ∩ X_b`.

The proof is the composite of three identifications: Mathlib's
`AlgebraicGeometry.Proj.awayι_preimage_basicOpen` turns `D₊(b)` into the basic open of the
fraction `bᵈ / aᵉ`, `Stacks.SectionRingChartOpen.chartRingMap_isLocalizationElem` evaluates the
chart ring map there, and `Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` turns the
resulting basic open of a ratio back into a nonvanishing open. -/
public theorem chartHomOn_preimage_projBasicOpen (hd : 0 < d) (hV : V ≤ nvOpen L a) {e : ℕ}
    (b : powSections L e) (he : 0 < e) :
    (chartHomOn L a hd hV).1 ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) e b)
      = V.ι ⁻¹ᵁ nvOpen L b := by
  obtain ⟨s, hs, hnv⟩ := exists_numerator L a hd b
  have hgen := Stacks.SectionRingChartMap.le_nvOpen_powSec L a hV (e + 1) (Nat.le_add_left 1 e)
  have hbasic : X.basicOpen (Stacks.SectionRingChartMap.ratio L (powSec L a (e + 1)) hgen s)
      = nvOpen L s ⊓ V :=
    (Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen
      (globalSection X _ (powSec L a (e + 1))) (globalSection X _ s) hgen _
      (Stacks.SectionRingChartMap.ratio_smul_resTop L (powSec L a (e + 1)) hgen s).symm).symm
  have hcoe : (ConcreteCategory.hom
        (CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a hV)))
          (HomogeneousLocalization.Away.isLocalizationElem
            (Stacks.ExternalGrading.of_mem_summand d a)
            (Stacks.ExternalGrading.of_mem_summand e b))
      = Stacks.SectionRingChartMap.ratio L (powSec L a (e + 1)) hgen s :=
    chartRingMap_isLocalizationElem L a hV b s hs
  rw [chartHomOn_val, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (grading L) (Stacks.ExternalGrading.of_mem_summand d a) hd
      (Stacks.ExternalGrading.of_mem_summand e b) he,
    SpecMap_preimage_basicOpen, hcoe, Scheme.Opens.toSpecΓ_preimage_basicOpen, hbasic, hnv,
    Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ι_preimage_eq_top hV,
    Scheme.Opens.ι_preimage_self, top_inf_eq, inf_top_eq]

end Monoidal

end Stacks.SectionRingChartOpen

end
