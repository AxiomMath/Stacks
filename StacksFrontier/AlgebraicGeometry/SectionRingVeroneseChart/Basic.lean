module

public import StacksFrontier.AlgebraicGeometry.Constructions.VeroneseSectionRing
public import StacksFrontier.AlgebraicGeometry.ChartDegreeEqualisation.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjFromSections

/-!
# The two charts of `Proj Γ_*(X, L)` at a homogeneous section are one chart

Let `X` be a scheme and `L` an invertible `𝒪_X`-module, and let `S = Γ_*(X, L)` be the graded
section ring of Stacks Tag 01CV. There are two constructions in this repository of a morphism
`X_a ⟶ Proj S` attached to a homogeneous `a ∈ S_d`, built for different purposes and never
compared:

* `Stacks.SectionRingChartMap.chartHom`, the chart of Stacks Tag 01PZ, out of which the canonical
  morphism `Stacks.SectionRingProjMorphism.projHomOfIsAmple` is glued. Its ring map is
  `Stacks.SectionRingChartMap.chartRingMap`, which sends the fraction `x / aⁿ` to the ratio
  `(a x) / a^{n+1}` of sections of tensor powers of `L`;
* `Stacks.MorphismToProj.HomogeneousRatios.chartToProj`, the chart of Stacks Tag 01N8, out of
  which the universal morphism of
  `Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair` is glued. Applied to the
  Veronese datum `Stacks.AlgebraicGeometry.ProjChartFromRatios.sectionRingVeronese` of the section
  ring itself, its ring map sends `x / aⁿ` to the ratio `ψ(x) / ψ(a)ⁿ` of sections of tensor
  powers of `L ^⊗ d`.

This file proves the two are the same morphism. Both are `U.toSpecΓ` followed by `Spec` of a ring
map out of `S_{(a)}` followed by `Proj.awayι`, so the comparison is an equality of **ring maps**,
and that equality is checked on the fractions `x / aⁿ`: both values are characterised as the
unique solution of a division, and the two divisions are carried onto one another by the Veronese
identification `Stacks.GradedSections.powPowIso`.

## Main results

* `Stacks.SectionRingVeroneseChart.lift_eq_chartRingMap`: **the two ring maps agree.**
* `Stacks.SectionRingVeroneseChart.chartToProj_eq_chartHom`: **the two charts agree**, as
  morphisms `X_a ⟶ Proj S`.
* `Stacks.SectionRingVeroneseChart.nonvanishingOpen_pow`: the nonvanishing open of the `n`-th
  power of the Veronese datum's trivializing section at `a` is the nonvanishing open `X_{aⁿ}`.

## Implementation notes

**The content is one division carried across the Veronese identification.** Writing `ψ` for the
Veronese datum of the section ring, the defining identity of the ratio
`c₁ = ψ(x) / ψ(a)ⁿ` is an identity of sections of `(L ^⊗ d) ^⊗ n` over `V`. The isomorphism
`Stacks.GradedSections.powPowIso` carries `(L ^⊗ d) ^⊗ n` to `L ^⊗ (d n)` and, by
`Stacks.SectionRingVeroneseChart.powPowIso_hom_app_toFun`, carries `ψ(x)` to `x` itself and
`ψ(a)ⁿ` to `aⁿ`; being a morphism of `𝒪_X`-modules it is `Γ(X, V)`-linear and commutes with
restriction, so the identity becomes `x|_V = c₁ · aⁿ|_V` in `L ^⊗ (d n)`. Multiplying by `a` —
`Stacks.AlgebraicGeometry.ProjChartFromRatios.resTop_mulSections_smul_left` — turns it into
`(a x)|_V = c₁ · a^{n+1}|_V`, which is the identity characterising
`Stacks.SectionRingChartMap.chartFamily`.

**No degree transport survives.** The Veronese datum is indexed by `𝒜 (n * d)` and the section
ring's powers by `d * n`; the single reindexing between them is
`Stacks.GradedSections.powCongr L (Nat.mul_comm n d)`, and
`Stacks.ChartDegreeEqualisation.of_comp_powCongr` makes it invisible in the ring, which is where
the numerators are named. The degree `d * (n + 1)` of `a^{n+1}` *is* the degree `d * n + d` that
multiplication produces, by `Nat.mul` recursing on its second argument.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open HomogeneousLocalization
open Stacks.AmpleFiniteAvoidance (grading nvOpen nvLocus)
open Stacks.GradedSections (powSections mul powCongr sectionRing)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionExtension (powSec)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.AlgebraicGeometry.ProjChartFromRatios

universe u

namespace Stacks.SectionRingVeroneseChart

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

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℕ)

/-! ### The Veronese datum, read back along the Veronese identification -/

/-- **The Veronese datum of the section ring recovers the section it came from.** The value
`ψ(z)` of `Stacks.AlgebraicGeometry.ProjChartFromRatios.sectionRingVeronese` on a homogeneous
element of degree `n d`, read along `Stacks.GradedSections.powPowIso` as a section of
`L ^⊗ (d n)`, is the global section named by any `s` with `DirectSum.of _ (d n) s = z`.

This is the definition of the datum unwound: it *is* a section composed with the inverse of the
identification, so composing with the identification cancels. -/
theorem powPowIso_hom_app_toFun (n : ℕ) (z : grading L (n * d)) (s : powSections L (d * n))
    (hs : DirectSum.of (powSections L) (d * n) s = (z : sectionRing L)) :
    (Stacks.GradedSections.powPowIso L d n).hom.app ⊤ ((sectionRingVeronese L d).toFun n z)
      = globalSection X (natTensorPow L (d * n)) s := by
  have hz : (Stacks.ExternalGrading.summandEquiv (powSections L) (n * d)).symm z
      ≫ powCongr L (Nat.mul_comm n d) = s :=
    comp_powCongr_eq_of_of_eq L (Nat.mul_comm n d) (by rw [of_piece, ← hs])
  change (Stacks.GradedSections.powPowIso L d n).hom.app ⊤ (veroneseToFun L d n z) = _
  rw [veroneseToFun_apply, hz, Stacks.GradedSections.ofPowPow_def,
    ← Stacks.SectionProduct.globalSection_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The powers of the Veronese datum's trivializing section at `a` are the powers of `a`**, read
along the Veronese identification. `powPowIso_hom_app_toFun` at the numerator `aⁿ`, whose two
spellings — the ring power of `DirectSum.of _ d a` and the section
`Stacks.SectionExtension.powSec` — are identified by
`Stacks.SectionRingChartMap.of_powSec_eq_pow`. -/
theorem powPowIso_hom_app_pow (a : powSections L d) (n : ℕ) :
    (Stacks.GradedSections.powPowIso L d n).hom.app ⊤
        ((sectionRingVeronese L d).pow (Stacks.ExternalGrading.of_mem_summand d a) n)
      = globalSection X (natTensorPow L (d * n)) (powSec L a n) :=
  powPowIso_hom_app_toFun L d n _ (powSec L a n)
    (Stacks.SectionRingChartMap.of_powSec_eq_pow L a n)

/-- **`Y_{ψ(a)ⁿ} = X_{aⁿ}`.** The nonvanishing open of the `n`-th power of the Veronese datum's
trivializing section at `a` is the nonvanishing open of `aⁿ` in the section ring's own
vocabulary. `Stacks.Ample.nonvanishingLocus_congr` for the Veronese identification, with
`powPowIso_hom_app_pow` naming the transported section. -/
theorem nonvanishingOpen_pow (a : powSections L d) (n : ℕ) :
    nonvanishingOpen X (natTensorPow (natTensorPow L d) n)
        ((sectionRingVeronese L d).pow (Stacks.ExternalGrading.of_mem_summand d a) n)
      = nvOpen L (powSec L a n) := by
  refine Opens.ext ?_
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, Stacks.AmpleFiniteAvoidance.coe_nvOpen]
  have h := Stacks.Ample.nonvanishingLocus_congr (Stacks.GradedSections.powPowIso L d n)
    ((sectionRingVeronese L d).pow (Stacks.ExternalGrading.of_mem_summand d a) n)
  rw [powPowIso_hom_app_pow] at h
  exact h.symm

/-- **An open inside `X_a` is inside the nonvanishing open of the Veronese datum's trivializing
section at `a`**, which is the hypothesis
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.homogeneousRatios` takes. The
degree-`1` case of `nonvanishingOpen_pow`, together with `X_a = X_{a¹}`. -/
theorem le_nonvanishingOpen_pow_one (a : powSections L d) {V : X.Opens} (hV : V ≤ nvOpen L a) :
    V ≤ nonvanishingOpen X (natTensorPow (natTensorPow L d) 1)
      ((sectionRingVeronese L d).pow (Stacks.ExternalGrading.of_mem_summand d a) 1) := by
  rw [nonvanishingOpen_pow]
  exact Stacks.SectionRingChartMap.le_nvOpen_powSec L a hV 1 le_rfl

/-! ### The two ring maps agree -/

/-- **The ring map of Stacks Tag 01N8's chart at `a`, for the Veronese datum of the section ring,
is the chart ring map of Stacks Tag 01PZ.** Both are ring maps
`S_{(a)} ⟶ Γ(X, V)` out of the degree-zero part of the localization of `Γ_*(X, L)` at
`DirectSum.of _ d a`, and both are determined by their values on the fractions `x / aⁿ`
(`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext`).

On such a fraction the first value is the ratio `ψ(x) / ψ(a)ⁿ` in `(L ^⊗ d) ^⊗ n` and the second
the ratio `(a x) / a^{n+1}` in `L ^⊗ (d (n+1))`. The Veronese identification turns the defining
identity of the first into `x|_V = c · aⁿ|_V`, multiplication by `a` turns that into
`(a x)|_V = c · a^{n+1}|_V`, and `Stacks.SectionRingChartMap.ratio_unique` reads off the
second. -/
theorem lift_eq_chartRingMap (a : powSections L d) (hd : 0 < d) {V : X.Opens}
    (hV : V ≤ nvOpen L a) :
    ((sectionRingVeronese L d).homogeneousRatios (Stacks.ExternalGrading.of_mem_summand d a)
        (le_nonvanishingOpen_pow_one L d a hV)).lift hd
      = Stacks.SectionRingChartMap.chartRingMap L a hV := by
  set hf := Stacks.ExternalGrading.of_mem_summand d a with hfdef
  set hW := le_nonvanishingOpen_pow_one L d a hV with hWdef
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext (grading L) hf fun n x hx => ?_
  have hxm : x ∈ grading L (n * d) := by simpa [smul_eq_mul] using hx
  -- name the numerator as a section of `L ^⊗ (d n)`
  set s : powSections L (d * n) :=
    (Stacks.ExternalGrading.summandEquiv (powSections L) (n * d)).symm
        (⟨x, hxm⟩ : grading L (n * d))
      ≫ powCongr L (Nat.mul_comm n d) with hsdef
  have hs : DirectSum.of (powSections L) (d * n) s = x := by
    rw [hsdef, Stacks.ChartDegreeEqualisation.of_comp_powCongr]
    exact of_piece L (n * d) ⟨x, hxm⟩
  -- the value of the first ring map, and its defining division
  set c : Γ(X, V) :=
    (sectionRingVeronese L d).ratio hf hW n ((sectionRingVeronese L d).toFun n ⟨x, hxm⟩) with hcdef
  have hlift : ((sectionRingVeronese L d).homogeneousRatios hf hW).lift hd
      (Away.mk (grading L) hf n x hx) = c :=
    ((sectionRingVeronese L d).homogeneousRatios hf hW).lift_mk hd n x hx ⟨x, hxm⟩ rfl
  have hdiv : resTop (natTensorPow (natTensorPow L d) n)
        ((sectionRingVeronese L d).toFun n ⟨x, hxm⟩) V
      = c • resTop (natTensorPow (natTensorPow L d) n)
          ((sectionRingVeronese L d).pow hf n) V :=
    (sectionRingVeronese L d).resTop_eq_ratio_smul hf hW n
      ((sectionRingVeronese L d).toFun n ⟨x, hxm⟩)
  -- carry it across the Veronese identification
  have hdiv' : resTop (natTensorPow L (d * n)) (globalSection X _ s) V
      = c • resTop (natTensorPow L (d * n)) (globalSection X _ (powSec L a n)) V := by
    have h := congrArg (fun y => (Stacks.GradedSections.powPowIso L d n).hom.app V y) hdiv
    simp only at h
    rw [← Stacks.TensorPowerTrivialize.resTop_app, Scheme.Modules.Hom.app_smul,
      ← Stacks.TensorPowerTrivialize.resTop_app,
      powPowIso_hom_app_toFun L d n ⟨x, hxm⟩ s hs, powPowIso_hom_app_pow L d a n] at h
    exact h
  -- multiply through by `a`
  have hmul : resTop (natTensorPow L (d * n + d)) (globalSection X _ (mul s a)) V
      = c • resTop (natTensorPow L (d * n + d))
          (globalSection X _ (mul (powSec L a n) a)) V := by
    have h := resTop_mulSections_smul_left L (globalSection X (natTensorPow L d) a) hdiv'
    rwa [mulSections_globalSection, mulSections_globalSection] at h
  -- read off the second ring map
  have hnum : DirectSum.of (powSections L) d a * x
      = DirectSum.of (powSections L) (d * (n + 1)) (mul s a) := by
    refine Eq.symm (Eq.trans (Stacks.SectionRingChartMap.of_mul_eq L s a) ?_)
    rw [hs, mul_comm]
  have hpow : V ≤ nvOpen L (powSec L a (n + 1)) :=
    Stacks.SectionRingChartMap.le_nvOpen_powSec L a hV (n + 1) (Nat.le_add_left 1 n)
  rw [hlift, Stacks.SectionRingChartMap.chartRingMap_mk,
    Stacks.SectionRingChartMap.chartFamily_apply, Stacks.SectionRingChartMap.numMapR_def, hnum,
    Stacks.SectionRingChartMap.ratioR_of]
  exact (Stacks.SectionRingChartMap.ratio_unique L (powSec L a (n + 1)) hpow (mul s a) c hmul).symm

/-! ### The two charts agree -/

/-- **Stacks Tag 01N8's chart at `a`, for the Veronese datum of the section ring, is Stacks Tag
01PZ's chart at `a`.** Both are `X_a ⟶ Spec Γ(X, X_a)` followed by `Spec` of a ring map out of
`S_{(a)}` followed by `AlgebraicGeometry.Proj.awayι`
(`Stacks.MorphismToProj.HomogeneousRatios.chartToProj` by definition,
`Stacks.SectionRingChartMap.chartHom` by
`Stacks.SectionRingChartOpen.chartHomOn_val`), so `lift_eq_chartRingMap` identifies them. -/
theorem chartToProj_eq_chartHom (a : powSections L d) (hd : 0 < d) :
    ((sectionRingVeronese L d).homogeneousRatios (Stacks.ExternalGrading.of_mem_summand d a)
        (le_nonvanishingOpen_pow_one L d a (le_refl (nvOpen L a)))).chartToProj hd
      = Stacks.SectionRingChartMap.chartHom L a hd := by
  rw [Stacks.MorphismToProj.HomogeneousRatios.chartToProj,
    Stacks.MorphismToProj.HomogeneousRatios.toSpecAway,
    lift_eq_chartRingMap L d a hd (le_refl (nvOpen L a)),
    ← Stacks.SectionRingChartOpen.chartHomOn_self L a hd,
    Stacks.SectionRingChartOpen.chartHomOn_val L a hd (le_refl (nvOpen L a)), Category.assoc]

end Monoidal

end Stacks.SectionRingVeroneseChart

end
