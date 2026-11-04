module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartOpen.Basic

/-!
# The charts of `Proj Γ_*(X, L)` agree on overlaps

For `a` and `b` homogeneous elements of positive degree of the graded section ring `Γ_*(X, L)` of
Stacks Tag 01CV, the construction of
`StacksFrontier/AlgebraicGeometry/SectionRingChartOpen/Basic.lean` gives two morphisms from an open
`V ⊆ X_a ∩ X_b` to `Proj Γ_*(X, L)`: the chart at `a` and the chart at `b`. This file proves they
are the same morphism, which is the compatibility the gluing of Stacks Tag 01PZ runs on.

They are both the chart at the **product** `ab`, whose nonvanishing open is `X_a ∩ X_b`
(`Stacks.SectionRingChartMap.nvOpen_mul`) and whose chart `D₊(ab)` is `D₊(a) ∩ D₊(b)`
(`Stacks.SectionRingProjOverlap.projBasicOpen_of_mul`). Mathlib supplies the geometry of that
refinement — `AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` says that the open immersion
`Spec (Γ_*(X, L)_{ab})₀ ⟶ Proj Γ_*(X, L)` factors through the one at `a` via the transition map
`HomogeneousLocalization.awayMap` — so all that is left is the corresponding statement about ring
maps, and that is the one theorem of this file.

## Main results

* `Stacks.SectionRingChartOpen.chartRingMap_comp_awayMap`: **the chart ring map at a product
  refines the chart ring map at a factor.** Composing the chart ring map at `c` with the
  transition map `(Γ_*(X, L)_g)₀ ⟶ (Γ_*(X, L)_c)₀`, for `c` a homogeneous element whose image in
  the ring is the product of the images of `g` and `h`, gives the chart ring map at `g`.
* `Stacks.SectionRingChartOpen.chartHomOn_eq_awayι`: the chart at `a` on an open inside
  `X_a ∩ X_b`, written as `Spec` of the chart ring map at `ab` followed by
  `AlgebraicGeometry.Proj.awayι`.
* `Stacks.SectionRingChartOpen.chartHomOn_eq`: **the charts agree.**

## Implementation notes

**The content is a cancellation.** On the fraction `y / gⁿ` the transition map multiplies both
numerator and denominator by `hⁿ`; the ratio is unchanged because
`Stacks.SectionRingChartMap.ratioR_mul` splits the ratio of a product and
`Stacks.SectionRingChartMap.ratioR_of_self` evaluates the spurious factor `hⁿ / hⁿ` to `1`. The
denominator of the refined fraction is `c^{n+1}`, of degree `m (n + 1)`, while the product of the
two denominators has degree `j (n + 1) + k (n + 1)`; the two are identified as *ring elements* by
`Stacks.SectionRingChartMap.ratioR_congr`, exactly as in
`StacksFrontier/AlgebraicGeometry/SectionRingChartMap/Multiplicative.lean`, so no section is ever
transported.

**The degree of the product is a hypothesis, not a literal sum.** `chartRingMap_comp_awayMap`
takes `hm : m = j + k` rather than fixing `m` to be `j + k`, and both
`Stacks.SectionRingChartOpen.chartRingMap_mk'` and `ratioR_congr` eliminate it by `subst` on a
variable. This is what lets the single theorem be applied to one and the same product `ab` with
its factors in **either** order: the two applications need the degree of `ab` to be `d + e` and
`e + d` respectively, and `Stacks.AlgebraicGeometry.ProjAwayChartFactor.awayι_congr` reconciles
the two spellings on the geometric side.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)

## What is not done

No `@[stacks]` attribute is attached: this is the overlap compatibility Stacks Tag 01PZ consumes,
not the statement of the tag, which is about the glued morphism and is in
`StacksFrontier/AlgebraicGeometry/SectionRingProjMorphism/Basic.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.GradedSections (powSections mul)
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

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens}

/-! ### The chart ring maps are compatible with the transition maps of the `Away` rings -/

/-- **The chart ring map at a product refines the chart ring map at a factor.** Let `c` be a
homogeneous element of `Γ_*(X, L)` whose image in the ring is the product of the images of `g` and
`h`, and let `V` be an open inside the three nonvanishing opens. Then the chart ring map at `c`,
precomposed with Mathlib's transition map `(Γ_*(X, L)_g)₀ ⟶ (Γ_*(X, L)_c)₀`, is the chart ring map
at `g`.

This is the whole content of the overlap condition for the gluing of Stacks Tag 01PZ: the
numerator and the denominator of a fraction `y / gⁿ` both acquire the factor `hⁿ` on passing to
`c`, and `Stacks.SectionRingChartMap.ratioR_mul` together with
`Stacks.SectionRingChartMap.ratioR_of_self` cancels it.

The degree `m` of `c` is not required to be the literal sum `j + k`, only to be equal to it; the
equation is spent by `Stacks.SectionRingChartOpen.chartRingMap_mk'` and by
`Stacks.SectionRingChartMap.ratioR_congr`, both of which eliminate it by `subst` on a variable.
This is what lets the lemma be applied to one and the same product with its two factors in either
order. -/
public theorem chartRingMap_comp_awayMap {j k m : ℕ} (g : powSections L j) (h : powSections L k)
    (c : powSections L m) (hm : m = j + k) (hVg : V ≤ nvOpen L g) (hVh : V ≤ nvOpen L h)
    (hVc : V ≤ nvOpen L c)
    (hc : DirectSum.of (powSections L) m c
      = DirectSum.of (powSections L) j g * DirectSum.of (powSections L) k h) :
    (Stacks.SectionRingChartMap.chartRingMap L c hVc).comp
        (HomogeneousLocalization.awayMap (grading L)
          (Stacks.ExternalGrading.of_mem_summand k h) hc)
      = Stacks.SectionRingChartMap.chartRingMap L g hVg := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading L)
    (Stacks.ExternalGrading.of_mem_summand j g) x
  -- the two generators, and the open they are both nonvanishing on
  have hGg := Stacks.SectionRingChartMap.le_nvOpen_powSec L g hVg (n + 1) (Nat.le_add_left 1 n)
  have hGh := Stacks.SectionRingChartMap.le_nvOpen_powSec L h hVh (n + 1) (Nat.le_add_left 1 n)
  have hGgh := Stacks.SectionRingChartMap.le_nvOpen_mul L hGg hGh
  -- the denominator `c^{n+1}`, as the product of the two denominators
  have hden : DirectSum.of (powSections L) (m * (n + 1)) (powSec L c (n + 1))
      = DirectSum.of (powSections L) (j * (n + 1) + k * (n + 1))
          (mul (powSec L g (n + 1)) (powSec L h (n + 1))) := by
    rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.of_mul_eq,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      hc, mul_pow]
  -- the numerator, with the acquired factor split off
  have hnum : DirectSum.of (powSections L) m c * (y * DirectSum.of (powSections L) k h ^ n)
      = DirectSum.of (powSections L) j g * y * DirectSum.of (powSections L) k h ^ (n + 1) := by
    rw [hc, pow_succ]
    ring
  have hz : DirectSum.of (powSections L) j g * y ∈ grading L (j * (n + 1)) := by
    rw [show j * (n + 1) = j + n • j from by rw [smul_eq_mul]; ring]
    exact SetLike.mul_mem_graded (Stacks.ExternalGrading.of_mem_summand j g) hy
  have hw : DirectSum.of (powSections L) k h ^ (n + 1) ∈ grading L (k * (n + 1)) := by
    rw [← Stacks.SectionRingChartMap.of_powSec_eq_pow]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  show Stacks.SectionRingChartMap.chartRingMap L c hVc
      (HomogeneousLocalization.awayMap (grading L)
        (Stacks.ExternalGrading.of_mem_summand k h) hc _) = _
  rw [HomogeneousLocalization.awayMap_mk, chartRingMap_mk' L c hVc hm.symm,
    Stacks.SectionRingChartMap.chartRingMap_mk, Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.chartFamily_apply, Stacks.SectionRingChartMap.numMapR_def,
    Stacks.SectionRingChartMap.numMapR_def,
    Stacks.SectionRingChartMap.ratioR_congr L (by rw [hm]; ring) (powSec L c (n + 1))
      (mul (powSec L g (n + 1)) (powSec L h (n + 1)))
      (Stacks.SectionRingChartMap.le_nvOpen_powSec L c hVc (n + 1) (Nat.le_add_left 1 n)) hGgh
      hden, hnum,
    Stacks.SectionRingChartMap.ratioR_mul L (powSec L g (n + 1)) (powSec L h (n + 1)) hGg hGh
      hGgh hz hw,
    ← Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.ratioR_of_self,
    mul_one]

/-! ### The charts agree -/

/-- The chart at a factor `g` of a homogeneous `c`, as `Spec` of the chart ring map at `c`
followed by `Proj.awayι`. -/
private theorem chartHomOn_eq_awayι_of_mul {j k m : ℕ} (g : powSections L j) (h : powSections L k)
    (c : powSections L m) (hm : m = j + k) (hj : 0 < j) (hm0 : 0 < m) (hVg : V ≤ nvOpen L g)
    (hVh : V ≤ nvOpen L h) (hVc : V ≤ nvOpen L c)
    (hc : DirectSum.of (powSections L) m c
      = DirectSum.of (powSections L) j g * DirectSum.of (powSections L) k h) :
    (chartHomOn L g hj hVg).1
      = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
            (Stacks.SectionRingChartMap.chartRingMap L c hVc)) ≫
          Proj.awayι (grading L) (DirectSum.of (powSections L) m c)
            (Stacks.ExternalGrading.of_mem_summand m c) hm0 := by
  rw [chartHomOn_val, ← chartRingMap_comp_awayMap L g h c hm hVg hVh hVc hc,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι (grading L) (Stacks.ExternalGrading.of_mem_summand j g) hj
      (Stacks.ExternalGrading.of_mem_summand k h) hc]
  rfl

/-- **The chart at a homogeneous element factors through the chart at a multiple of it.** On an
open inside both `X_a` and `X_b`, the chart at `a` is the composite of `Spec` of the chart ring map
at the product `ab` with Mathlib's open immersion `Spec (Γ_*(X, L)_{ab})₀ ⟶ Proj Γ_*(X, L)`. -/
public theorem chartHomOn_eq_awayι {d e : ℕ} (a : powSections L d) (b : powSections L e)
    (hd : 0 < d) (hVa : V ≤ nvOpen L a) (hVb : V ≤ nvOpen L b)
    (hV : V ≤ nvOpen L (mul a b)) (hde : 0 < d + e) :
    (chartHomOn L a hd hVa).1
      = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
            (Stacks.SectionRingChartMap.chartRingMap L (mul a b) hV)) ≫
          Proj.awayι (grading L) (DirectSum.of (powSections L) (d + e) (mul a b))
            (Stacks.ExternalGrading.of_mem_summand (d + e) (mul a b)) hde := by
  exact chartHomOn_eq_awayι_of_mul L a b (mul a b) rfl hd hde hVa hVb hV
    (Stacks.SectionRingChartMap.of_mul_eq L a b)

/-- **The charts of `Proj Γ_*(X, L)` agree on overlaps.** For `a` and `b` homogeneous of positive
degrees and `V` an open inside both `X_a` and `X_b`, the chart at `a` and the chart at `b` are the
same morphism `V ⟶ Proj Γ_*(X, L)`: both are the chart at the product `ab`, whose nonvanishing
open is `X_a ∩ X_b`.

This is the compatibility the gluing of Stacks Tag 01PZ runs on. -/
public theorem chartHomOn_eq {d e : ℕ} (a : powSections L d) (b : powSections L e) (hd : 0 < d)
    (he : 0 < e) (hVa : V ≤ nvOpen L a) (hVb : V ≤ nvOpen L b) :
    (chartHomOn L a hd hVa).1 = (chartHomOn L b he hVb).1 := by
  have hV : V ≤ nvOpen L (mul a b) := Stacks.SectionRingChartMap.le_nvOpen_mul L hVa hVb
  have hde : 0 < d + e := by omega
  refine (chartHomOn_eq_awayι L a b hd hVa hVb hV hde).trans ?_
  exact (chartHomOn_eq_awayι_of_mul L b a (mul a b) (Nat.add_comm d e) he hde hVb hVa hV
    ((Stacks.SectionRingChartMap.of_mul_eq L a b).trans (mul_comm _ _))).symm

end Monoidal

end Stacks.SectionRingChartOpen

end
