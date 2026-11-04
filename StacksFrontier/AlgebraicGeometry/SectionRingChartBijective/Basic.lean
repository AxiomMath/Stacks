module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Annihilator
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Ratio
public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Chart

/-!
# The chart ring map is bijective: Stacks Tag 01PW at arbitrary degree, for the structure sheaf

Let `X` be a scheme, `L` an **ample** invertible `𝒪_X`-module and `a` a homogeneous element of
positive degree `d` of the graded section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag
01CV. `Stacks.SectionRingChartMap.chartRingMap` is the ring homomorphism

`Γ_*(X, L)₍a₎ = HomogeneousLocalization.Away (grading L) a ⟶ Γ(X, X_a)`

out of which the chart `X_a ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is built. This file proves that
it is **bijective**, which is the "in particular" of Stacks Tag 01PW — the case `𝓕 = 𝒪_X` — at the
arbitrary degree `d`.

## How the two halves are discharged

`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective` and
`..._surjective` reduce bijectivity of a lifted ring map to two statements about *numerators*, and
those are the two files this one sits on:

* injectivity needs a numerator annihilated by its member of the family to be annihilated by a
  power of `a` in the ring, which is
  `Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero`;
* surjectivity needs every function on `X_a` to be the value of the family on some numerator,
  which is `Stacks.SectionRingChartBijective.exists_ratio_powSec`.

Both are translated here into the vocabulary of the family
`Stacks.SectionRingChartMap.chartFamily`, whose `n`-th member is `(a · z) / a^{n+1}` — the
exponent shift of `StacksFrontier/AlgebraicGeometry/SectionRingChartMap/Normalization.lean`. The
shift is why the surjectivity translation goes through
`Stacks.SectionRingChartMap.numMapR_of_mul` rather than through a division: the ratio by `aᵐ`
produced by the geometry is *equal* to the ratio of `a · z` by `a^{m+1}`, so no numerator has to
be divided by `a`.

**No degree transport occurs.** The geometry returns its denominator as a power of a power,
`(a^{N₀})^m`, in the degree `d N₀ m`, while the family divides by `a^{N₀ m}`, in the degree
`d (N₀ m)`; the two are identified by `Stacks.SectionRingChartMap.ratioR_congr`, which compares
two generators of equal — not identical — degree through their images in the ring and eliminates
the degree equation by `subst` on a variable.

## Main results

* `Stacks.SectionRingChartBijective.exists_pow_mul_of_chartFamily_eq_zero`: the injectivity
  hypothesis of the lift, for the chart family.
* `Stacks.SectionRingChartBijective.exists_chartFamily_eq`: the surjectivity hypothesis of the
  lift, for the chart family.
* `Stacks.SectionRingChartBijective.chartRingMap_bijective`: **the chart ring map at a
  homogeneous element of positive degree is bijective, for `L` ample.**

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec resTop nvLocus_powSec_of_one_le)

universe u

namespace Stacks.SectionRingChartBijective

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

/-! ### The numerator of the shifted family -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **The numerator the chart family divides.** For `z` homogeneous of degree `n d`, the product
`a · z` is homogeneous of degree `d (n + 1)`; this names it as a section of that degree, by
reading a membership off the ring equation rather than transporting a section. -/
theorem exists_shift_numerator {d : ℕ} (a : powSections L d) (n : ℕ) {z : sectionRing L}
    (hz : z ∈ grading L (n * d)) :
    ∃ t : powSections L (d * (n + 1)),
      DirectSum.of (powSections L) (d * (n + 1)) t
        = DirectSum.of (powSections L) d a * z := by
  have hmem : DirectSum.of (powSections L) d a * z ∈ grading L (d * (n + 1)) := by
    have h : DirectSum.of (powSections L) d a * z ∈ grading L (d + n * d) :=
      SetLike.mul_mem_graded (Stacks.ExternalGrading.of_mem_summand d a) hz
    rwa [show d * (n + 1) = d + n * d from by ring]
  exact Stacks.ExternalGrading.mem_summand_iff.mp hmem

/-! ### The injectivity hypothesis -/

/-- **A numerator killed by the chart family is killed by a power of `a`.** This is the hypothesis
`hker` of `Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective` for the chart
family at `a`: the family sends a numerator to the ratio of `a · z` by a power of `a`, so the
numerator restricts to zero on `X_a`, and
`Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero` annihilates it. -/
theorem exists_pow_mul_of_chartFamily_eq_zero (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    (a : powSections L d) (n : ℕ) (z : sectionRing L) (hz : z ∈ grading L (n * d))
    (h0 : Stacks.SectionRingChartMap.chartFamily L a (le_refl (nvOpen L a)) n z = 0) :
    ∃ k : ℕ, DirectSum.of (powSections L) d a ^ k * z = 0 := by
  obtain ⟨t, ht⟩ := exists_shift_numerator L a n hz
  have hnum : Stacks.SectionRingChartMap.numMap L a (le_refl (nvOpen L a)) (n + 1)
      (Nat.le_add_left 1 n) (globalSection X _ t) = 0 := by
    rw [← Stacks.SectionRingChartMap.chartFamily_eq_numMap L a (le_refl (nvOpen L a)) n z t ht]
    exact h0
  have hres : resTop (nvOpen L a) (globalSection X _ t) = 0 := by
    have h := Stacks.SectionRingChartMap.numMap_smul_resTop L a (le_refl (nvOpen L a)) (n + 1)
      (Nat.le_add_left 1 n) (globalSection X _ t)
    rw [hnum, zero_smul] at h
    exact h.symm
  obtain ⟨k, hk⟩ := exists_pow_mul_of_eq_zero L hL hd a t hres
  refine ⟨k + 1, ?_⟩
  have hcalc : DirectSum.of (powSections L) d a ^ (k + 1) * z
      = DirectSum.of (powSections L) (d * (n + 1)) t
        * DirectSum.of (powSections L) d a ^ k := by
    rw [ht]; ring
  rw [hcalc, hk]

/-! ### The surjectivity hypothesis -/

/-- **Every function on `X_a` is a value of the chart family.** This is the hypothesis `hsurj` of
`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_surjective` for the chart family at
`a`.

The geometry (`Stacks.SectionRingChartBijective.exists_ratio_powSec`) produces the function as a
ratio with denominator `(a^{N₀})^m`; `Stacks.SectionRingChartMap.ratioR_congr` replaces that
generator by `a^{N₀ m}`, whose degree is the same number written differently, and
`Stacks.SectionRingChartMap.numMapR_of_mul` absorbs the exponent shift of the family. -/
theorem exists_chartFamily_eq (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d)
    (y : Γ(X, nvOpen L a)) :
    ∃ (n : ℕ) (z : sectionRing L), z ∈ grading L (n * d) ∧
      Stacks.SectionRingChartMap.chartFamily L a (le_refl (nvOpen L a)) n z = y := by
  obtain ⟨N₀, m, hN₀, hm, t, ht⟩ := exists_ratio_powSec L hL hd a y
  have hnm : 1 ≤ N₀ * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hb : nvOpen L a ≤ nvOpen L (powSec L (powSec L a N₀) m) :=
    Stacks.SectionRingChartMap.le_nvOpen_powSec L _
      (Stacks.SectionRingChartMap.le_nvOpen_powSec L a le_rfl N₀ hN₀) m hm
  have hb' : nvOpen L a ≤ nvOpen L (powSec L a (N₀ * m)) :=
    Stacks.SectionRingChartMap.le_nvOpen_powSec L a le_rfl (N₀ * m) hnm
  -- the ratio the geometry produced
  have hratio : Stacks.SectionRingChartMap.ratio L (powSec L (powSec L a N₀) m) hb t = y :=
    Stacks.SectionRingChartMap.ratio_unique L _ hb t y ht
  -- the two generators have the same image in the ring
  have hofB : DirectSum.of (powSections L) (d * N₀ * m) (powSec L (powSec L a N₀) m)
      = DirectSum.of (powSections L) (d * (N₀ * m)) (powSec L a (N₀ * m)) := by
    rw [Stacks.SectionRingChartMap.of_powSec_eq_pow L (powSec L a N₀) m,
      Stacks.SectionRingChartMap.of_powSec_eq_pow L a N₀,
      Stacks.SectionRingChartMap.of_powSec_eq_pow L a (N₀ * m), pow_mul]
  have hcongr := Stacks.SectionRingChartMap.ratioR_congr L (Nat.mul_assoc d N₀ m)
    (powSec L (powSec L a N₀) m) (powSec L a (N₀ * m)) hb hb' hofB
    (DirectSum.of (powSections L) (d * N₀ * m) t)
  have hfinal : Stacks.SectionRingChartMap.ratioR L (powSec L a (N₀ * m)) hb'
      (DirectSum.of (powSections L) (d * N₀ * m) t) = y := by
    rw [← hcongr, Stacks.SectionRingChartMap.ratioR_of]
    exact hratio
  have hz1 : DirectSum.of (powSections L) (d * N₀ * m) t ∈ grading L (d * (N₀ * m)) := by
    rw [← Nat.mul_assoc]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  have hz2 : DirectSum.of (powSections L) (d * N₀ * m) t ∈ grading L (N₀ * m * d) := by
    rw [show N₀ * m * d = d * N₀ * m from by ring]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  refine ⟨N₀ * m, DirectSum.of (powSections L) (d * N₀ * m) t, hz2, ?_⟩
  calc Stacks.SectionRingChartMap.chartFamily L a (le_refl (nvOpen L a)) (N₀ * m)
          (DirectSum.of (powSections L) (d * N₀ * m) t)
      = Stacks.SectionRingChartMap.numMapR L a (le_refl (nvOpen L a)) (N₀ * m + 1)
          (Nat.le_add_left 1 (N₀ * m)) (DirectSum.of (powSections L) d a
            * DirectSum.of (powSections L) (d * N₀ * m) t) := rfl
    _ = Stacks.SectionRingChartMap.numMapR L a (le_refl (nvOpen L a)) (N₀ * m) hnm
          (DirectSum.of (powSections L) (d * N₀ * m) t) :=
        Stacks.SectionRingChartMap.numMapR_of_mul L a (le_refl (nvOpen L a)) (N₀ * m) hnm
          (Nat.le_add_left 1 (N₀ * m)) hz1
    _ = y := by
        rw [Stacks.SectionRingChartMap.numMapR_def]
        exact hfinal

/-! ### Bijectivity -/

/-- **The chart ring map at a homogeneous element of positive degree is bijective, for `L`
ample.** This is the "in particular" of Stacks Tag 01PW — the case `𝓕 = 𝒪_X` — at the arbitrary
degree of `a`: the degree-zero part of the localization of `Γ_*(X, L)` at `a` is the ring of
functions on the nonvanishing open `X_a`.

Ampleness is used only through the two numerator statements; it supplies the finite affine cover
by nonvanishing opens that the proof of Tag 01PW runs over. -/
theorem chartRingMap_bijective (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d) :
    Function.Bijective
      (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a))) :=
  ⟨Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a)
      (Stacks.SectionRingChartMap.chartFamily L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_pow_mul L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_one L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_mul L a (le_refl (nvOpen L a)))
      (fun n z hz h0 ↦ exists_pow_mul_of_chartFamily_eq_zero L hL hd a n z hz h0),
    Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_surjective (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a)
      (Stacks.SectionRingChartMap.chartFamily L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_pow_mul L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_one L a (le_refl (nvOpen L a)))
      (Stacks.SectionRingChartMap.chartFamily_mul L a (le_refl (nvOpen L a)))
      (fun y ↦ exists_chartFamily_eq L hL hd a y)⟩

end Monoidal

end Stacks.SectionRingChartBijective

end
