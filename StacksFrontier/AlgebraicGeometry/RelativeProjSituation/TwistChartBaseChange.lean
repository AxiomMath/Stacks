module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartHypothesisBaseChange
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.DegreewiseBaseChange

/-!
# The twist comparison of a relative `Proj` base change, on a chart

Let `g : S' ⟶ S` be a morphism of schemes, let `s` and `s'` be relative `Proj` situations over
`S` and `S'`, and let `Φ` identify the graded algebra of `s'` with the pullback along `g` of the
graded algebra of `s`, isomorphically in every nonnegative degree — the situation of
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/BaseChangeGluing.lean`. For a pair of affine
opens `W' ⊆ g⁻¹W` the base change of graded section rings
`Stacks.RelativeProj.Situation.gradedBaseChange` induces a morphism of charts
`Proj 𝒜'(W') ⟶ Proj 𝒜(W)`, and Tag 01MY attaches to it a comparison map

`θ n : (Proj.map φ)^* 𝒪_{Proj 𝒜(W)}(n) ⟶ 𝒪_{Proj 𝒜'(W')}(n)`

on every twisting sheaf. This file proves that each `θ n` is an **isomorphism**. That is the
chart-level content of the second assertion of Tag 01O3, the graded isomorphism `θ` on the
twisting sheaves of a relative `Proj` base change.

## The route

Invertibility is local on `Proj 𝒜'(W')`, which is covered by the charts `D₊(φ f)` with `f`
homogeneous of positive degree because the domain of definition of `φ` is everything, and on such
a chart the comparison is the coefficient extension of the algebraic chart comparison, by
`Stacks.AlgebraicGeometry.TwistChartLocality`'s
`isIso_pullback_awayι_map_twistMap_of_isIso_chartExtension`. That extension is invertible because
`φ` is a base change **degreewise** — the degree-`n` sections of `𝒜'` over `W'` are the base
change of those of `𝒜` over `W`, which is
`Stacks.RelativeProj.Situation.isBaseChange_pieceMap_gradedBaseChange` — and the twist of a
degreewise base change is one too, which is
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_twistDegreeZeroExtension_of_isBaseChange`.

No freeness and no degree-one hypothesis enters, so the result holds for an arbitrary relative
`Proj` situation and every `n : ℤ`, exactly as clause (3) of Tag 01N2 does for a base change of
an absolute `Proj`.

## Main results

* `Stacks.RelativeProj.Situation.isIso_twistMap_gradedBaseChange`: **the twist comparison
  attached to a pair of affine opens of a relative `Proj` base change is an isomorphism**, in
  every degree.

## What this does not prove

No tag attribute is attached. Tag 01O3's twist assertion is a graded isomorphism on the twisting
sheaves of the two relative projective spectra, and what is proved here is its restriction to one
chart; gluing the chart comparisons into a morphism
`r^* 𝒪_{Proj_S(𝒜)}(n) ⟶ 𝒪_{Proj_{S'}(𝒜')}(n)` on all of `Proj_{S'}(𝒜')` is the content of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChange.lean` and its
companions, run for the twisting sheaves instead of for the sheaf of a graded module. The scheme
half of the tag is `Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange`.

The sibling `Stacks.RelativeProj.Situation.isIso_twistMap_gradedSectionRestriction` is the same
statement for the *restriction* map of one situation along an inclusion of affine opens of its
base, Tag 01NO's twist assertion; that one is proved from bijectivity on sections, which is
false here — a base change of the base scheme is not an open immersion — and is why the chart
criterion is used instead.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.TwistChartLocality

universe u

namespace Stacks.RelativeProj.Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))

/-- **The twist comparison attached to a pair of affine opens of a relative `Proj` base change is
an isomorphism**, in every degree `n : ℤ`.

For affine opens `W` of `S` and `W' ⊆ g⁻¹W` of `S'`, Tag 01MY's comparison map on the `n`-th
twisting sheaf across the chart morphism `Proj 𝒜'(W') ⟶ Proj 𝒜(W)` induced by
`Stacks.RelativeProj.Situation.gradedBaseChange` is invertible. This is the chart-level content of
the twist assertion of Tag 01O3; no hypothesis beyond the situation and the datum `Φ` is
carried. -/
public theorem isIso_twistMap_gradedBaseChange (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) (n : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (gradedBaseChange g Φ W.1 W'.1 h)
      (irrelevant_le_gradedBaseChange g Φ W W' h hΦ) n) := by
  let aCD : Algebra ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) :=
    ((gradedBaseChange g Φ W.1 W'.1 h).gradedZeroRingHom).toAlgebra
  have halgCD : ∀ a : ↥(s.sectionRingGrading W.1 0),
      algebraMap ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) a
        = (gradedBaseChange g Φ W.1 W'.1 h).gradedZeroRingHom a := fun _ => rfl
  have halgAB : ∀ r : ↥(s.sectionRingGrading W.1 0),
      ((algebraMap ↥(s.sectionRingGrading W.1 0) ↥(s'.sectionRingGrading W'.1 0) r :
          s'.sectionRing W'.1))
        = gradedBaseChange g Φ W.1 W'.1 h (r : s.sectionRing W.1) := fun _ => rfl
  have hle := irrelevant_le_gradedBaseChange g Φ W W' h hΦ
  exact isIso_projTwistComparison_of_forall_pullback_awayι_of_mapDomain_eq_top
    (s.sectionRingGrading W.1) (s'.sectionRingGrading W'.1) (gradedBaseChange g Φ W.1 W'.1 h)
    hle (mapDomain_eq_top_of_irrelevant_le_map _ _ _ hle) n fun d hd f hf =>
      isIso_pullback_awayι_map_twistMap_of_isIso_chartExtension _ _ _ hle hd hf n
        (isIso_twistDegreeZeroExtension_of_isBaseChange _ n halgAB hf
          fun k => isBaseChange_pieceMap_gradedBaseChange g Φ k W.2 W'.2 h hΦ halgCD halgAB)

end Stacks.RelativeProj.Situation

end
