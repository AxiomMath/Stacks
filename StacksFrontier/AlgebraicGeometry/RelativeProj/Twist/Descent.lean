module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Local

/-!
# Descent of the twist comparison to a general affine open

In a relative `Proj` situation, let `W ≤ W'` be affine opens of the base and let
`r : Proj 𝒜(W) ⟶ Proj 𝒜(W')` be the comparison morphism of charts. This file proves that the
canonical comparison `θ : r^* 𝒪_{Proj 𝒜(W')}(n) ⟶ 𝒪_{Proj 𝒜(W)}(n)` of
`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Comparison.lean` is an isomorphism, for every
`n : ℤ`. This is the remaining clause of Stacks tag 01NO about the isomorphisms `θ`.

`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Iso.lean` settles the case where the graded
restriction map is a degreewise localization away from a degree-zero element, which by
`Stacks.RelativeProj.Situation.isAwayDegreewise_basicOpen` is the case where `W` is a *standard*
open `D(g)` of `W'`. The descent is the covering argument that
`StacksFrontier/AlgebraicGeometry/RelativeProj/Charts/Descent.lean` uses for the cartesian square:
the standard opens `D(g)` of `W'` contained in `W` cover `W`, and each of them is also a standard
open of `W`, so the restriction `𝒜(W') → 𝒜(D(g))` factors as `𝒜(W') → 𝒜(W) → 𝒜(D(g))` with both
the composite and the second factor degreewise localizations.

That factorization carries the two hypotheses of
`Stacks.ProjTwistComparison.bijective_sectionsMap_of_cover` across:

* at a point, the fibre comparison of the middle map is bijective because the composite's is and
  the second factor's is injective; every point of `Proj 𝒜(W)` lies over a point of `W`, hence
  in some `D(g)`, so this covers all of `Proj 𝒜(W)`;
* over an open contained in `D₊(g)`, the comparison on sections of the middle map is surjective
  for the same reason, this time at the level of sections.

Bijectivity on sections over an arbitrary open of the image then follows because it is local,
and `Stacks.ProjTwistComparison.isIso_twistMap_of_bijective` turns it into `IsIso θ`.

## Main results

* `Stacks.RelativeProj.Situation.bijective_fibreMap_gradedSectionRestriction`: the fibre
  comparison of the graded restriction map is bijective at every point of the smaller chart.
* `Stacks.RelativeProj.Situation.bijective_sectionsMap_gradedSectionRestriction`: the comparison
  on sections is bijective over every open of the chart over `W'` lying in the image of the
  chart over `W`.
* `Stacks.RelativeProj.Situation.isIso_twistMap_gradedSectionRestriction`: **the twist comparison
  attached to an inclusion of affine opens of the base is an isomorphism.**

## Implementation notes

The element of `𝒜(W)₀` that the restriction to `D(g)` is a degreewise localization away from is
written as the image of `s.sectionRingBaseMap W' g` under the restriction `𝒜(W') → 𝒜(W)`, rather
than as `s.sectionRingBaseMap W` of the restricted section. The two agree by
`Stacks.RelativeProj.Situation.gradedSectionRestriction_baseMap`, but the first form is the one
in which non-vanishing at a point of `Proj 𝒜(W)` is read off from non-vanishing at its image in
`Proj 𝒜(W')`, with no rewriting under the homogeneous ideal.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjTwistComparison Stacks.GradedLocalization

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The two degreewise localizations attached to a standard open -/

/-- The graded restriction map to an affine open presented as a standard open by an equation is
a degreewise localization. -/
public theorem isAwayDegreewise_of_eq_basicOpen {W W' : s.base.Opens} (hW' : IsAffineOpen W')
    (g : Γ(s.base, W')) (hWeq : W = s.base.basicOpen g) (hle : W ≤ W') :
    IsAwayDegreewise (gradedSectionRestriction s W W' hle) (s.sectionRingBaseMap W' g) := by
  subst hWeq
  exact isAwayDegreewise_basicOpen s g hW'

/-- The graded restriction map carries the image of a function on the base to the image of its
restriction, in the spelling `Stacks.RelativeProj.Situation.gradedSectionRestriction_baseMap`
leaves implicit. -/
public theorem gradedSectionRestriction_baseMap' {U V : s.base.Opens} (h : U ≤ V)
    (r : Γ(s.base, V)) :
    (gradedSectionRestriction s U V h) (s.sectionRingBaseMap V r) =
      s.sectionRingBaseMap U (s.base.presheaf.map (homOfLE h).op r) :=
  gradedSectionRestriction_baseMap s U V h r

/-- **The restriction `𝒜(W) → 𝒜(D(g))` is a degreewise localization away from the image of `g`.**
A standard open of `W'` contained in `W` is a standard open of `W`. -/
public theorem isAwayDegreewise_restrictOfBase {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (g : Γ(s.base, W')) (hgle : s.base.basicOpen g ≤ W) :
    IsAwayDegreewise (gradedSectionRestriction s (s.base.basicOpen g) W hgle)
      ((gradedSectionRestriction s W W' h) (s.sectionRingBaseMap W' g)) := by
  rw [gradedSectionRestriction_baseMap' s h g]
  refine isAwayDegreewise_of_eq_basicOpen s hW (s.base.presheaf.map (homOfLE h).op g) ?_ hgle
  rw [Scheme.basicOpen_res, inf_eq_right.mpr hgle]

/-- The restriction of a chart along an inclusion of affine opens is, at the level of points,
the comparison of homogeneous spectra. -/
public theorem base_projInclusionMap (U V : s.base.Opens) (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (z : ProjectiveSpectrum (s.sectionRingGrading U)) :
    (projInclusionMap s U V hUV hU hV).base z =
      ProjectiveSpectrum.comapFun (gradedSectionRestriction s U V hUV)
        (irrelevant_le_map_gradedSectionRestriction s U V hUV hU hV) z := rfl

/-- The comparison morphism of charts does not change the image of a point in the base. -/
public theorem chartToBase_projInclusion {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (z : ↥(AlgebraicGeometry.Proj (s.sectionRingGrading W))) :
    chartToBase s W' hW' (projInclusionMap s W W' h hW hW' z) = chartToBase s W hW z := by
  rw [← Scheme.Hom.comp_apply, projInclusionMap_comp_chartToBase]

/-- The standard opens of `W'` that lie in `W` give the standard opens of the chart over `W'`
through which the covering argument runs. -/
public theorem basicOpen_eq_chartToBase_preimage {W' : s.base.Opens} (hW' : IsAffineOpen W')
    (g : Γ(s.base, W')) :
    AlgebraicGeometry.Proj.basicOpen (s.sectionRingGrading W') (s.sectionRingBaseMap W' g) =
      chartToBase s W' hW' ⁻¹ᵁ s.base.basicOpen g := by
  rw [← projInclusionToOpen_preimage s g hW',
    projInclusionToOpen_preimage_opensRange s (s.base.basicOpen g) W'
      (s.base.basicOpen_le g) hW']

/-! ### The descent -/

/-- Every point of the chart over `W` lies over a standard open of `W'` contained in `W`. -/
private theorem exists_basicOpen_le_chartToBase {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W)) :
    ∃ (g : Γ(s.base, W')) (_ : s.base.basicOpen g ≤ W),
      chartToBase s W hW y ∈ s.base.basicOpen g := by
  have hyW : chartToBase s W hW y ∈ W := chartToBase_mem s W hW y
  obtain ⟨g, hgle, hgy⟩ := hW'.exists_basicOpen_le (⟨chartToBase s W hW y, hyW⟩ : W) (h hyW)
  exact ⟨g, hgle, hgy⟩

/-- Every point of the chart over `W` lies in the image of the chart over a standard open of
`W'` contained in `W`. -/
public theorem exists_chart_point {W W' : s.base.Opens} (h : W ≤ W') (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (y : ProjectiveSpectrum (s.sectionRingGrading W)) :
    ∃ (g : Γ(s.base, W')) (hg : s.base.basicOpen g ≤ W)
      (z : ProjectiveSpectrum (s.sectionRingGrading (s.base.basicOpen g))),
      ProjectiveSpectrum.comapFun (gradedSectionRestriction s (s.base.basicOpen g) W hg)
        (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W hg
          (hW'.basicOpen g) hW) z = y := by
  obtain ⟨g, hgle, hgy⟩ := exists_basicOpen_le_chartToBase s h hW hW' y
  have hoi := isOpenImmersion_projInclusionMap s hgle (hW'.basicOpen g) hW
  have hrange := opensRange_projInclusionMap s hgle (hW'.basicOpen g) hW
  have hy : y ∈
      (projInclusionMap s (s.base.basicOpen g) W hgle (hW'.basicOpen g) hW).opensRange := by
    rw [hrange]
    exact hgy
  obtain ⟨z, hz⟩ := hy
  exact ⟨g, hgle, z, hz⟩

/-- **The fibre comparison of the graded restriction map is bijective.** At a point `y` of the
chart over `W`, choose a standard open `D(g)` of `W'` inside `W` over which `y` lies. Both
`𝒜(W') → 𝒜(D(g))` and `𝒜(W) → 𝒜(D(g))` are degreewise localizations, so the first's fibre
comparison is bijective and the second's is injective; the first is the second composed with the
fibre comparison of `𝒜(W') → 𝒜(W)`, so the latter is bijective. -/
theorem bijective_fibreMap_gradedSectionRestriction {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W)) :
    Function.Bijective (fibreMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') y) := by
  obtain ⟨g, hgle, z, hz⟩ := exists_chart_point s h hW hW' y
  subst hz
  refine bijective_fibreMap_of_eq_comp (gradedSectionRestriction s W W' h)
    (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW')
    (gradedSectionRestriction s (s.base.basicOpen g) W hgle)
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW)
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W' (hgle.trans h)
      (hW'.basicOpen g) hW')
    (gradedSectionRestriction_comp s (s.base.basicOpen g) W W' hgle h) z ?_ ?_
  · exact (isAwayDegreewise_basicOpen s g hW').bijective_localRingHom _ _ rfl
  · exact (isAwayDegreewise_restrictOfBase s h hW g hgle).injective_localRingHom _ _ rfl

/-- **The comparison on sections is surjective over an open where `g` does not vanish.** The
factorization used for the fibres, read on sections: the composite `𝒜(W') → 𝒜(D(g))` is bijective
on sections over such an open, and `𝒜(W) → 𝒜(D(g))` is injective on sections over its preimage,
so `𝒜(W') → 𝒜(W)` is surjective. -/
private theorem surjective_sectionsMap_of_basicOpen {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (n : ℤ) (g : Γ(s.base, W'))
    (hgle : s.base.basicOpen g ≤ W)
    (V : Opens (ProjectiveSpectrum.top (s.sectionRingGrading W')))
    (hV : V ≤ AlgebraicGeometry.Proj.basicOpen (s.sectionRingGrading W')
      (s.sectionRingBaseMap W' g)) :
    Function.Surjective (sectionsMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') n V) := by
  have hmem := fun x : V => (AlgebraicGeometry.Proj.mem_basicOpen (s.sectionRingGrading W')
    (s.sectionRingBaseMap W' g) x.1).mp (hV x.2)
  refine surjective_sectionsMap_of_eq_comp (gradedSectionRestriction s W W' h)
    (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') n
    (gradedSectionRestriction s (s.base.basicOpen g) W hgle)
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW)
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W' (hgle.trans h)
      (hW'.basicOpen g) hW')
    (gradedSectionRestriction_comp s (s.base.basicOpen g) W W' hgle h) V ?_ ?_
  · refine (bijective_sectionsMap _ (isAwayDegreewise_basicOpen s g hW')
      (sectionRingBaseMap_mem_zero s W' g) _ n V hmem).2
  · refine injective_sectionsMap _ (isAwayDegreewise_restrictOfBase s h hW g hgle)
      ((gradedSectionRestriction s W W' h).map_mem (sectionRingBaseMap_mem_zero s W' g)) _ n _
      fun x => hmem ⟨_, x.2⟩

/-- **The comparison on sections of the graded restriction map is bijective** over every open of
the chart over `W'` whose points come from the chart over `W`. The opens `D₊(g) ⊓ U`, for `g` a
section over `W'` with `D(g) ≤ W`, cover `U`, and over each of them the comparison is surjective;
the fibre comparison is bijective everywhere. -/
theorem bijective_sectionsMap_gradedSectionRestriction {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (n : ℤ)
    (U : Opens (ProjectiveSpectrum.top (s.sectionRingGrading W')))
    (hU : ∀ x : U, ∃ y : ProjectiveSpectrum (s.sectionRingGrading W),
      ProjectiveSpectrum.comapFun (gradedSectionRestriction s W W' h)
        (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') y = x.1) :
    Function.Bijective (sectionsMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') n U) := by
  refine bijective_sectionsMap_of_cover _ _ n U
    (ι := {g : Γ(s.base, W') // s.base.basicOpen g ≤ W})
    (fun g => AlgebraicGeometry.Proj.basicOpen (s.sectionRingGrading W')
      (s.sectionRingBaseMap W' g.1) ⊓ U)
    (fun _ => inf_le_right) (fun x => ?_) hU
    (fun y => (bijective_fibreMap_gradedSectionRestriction s h hW hW' y).1)
    (fun g => surjective_sectionsMap_of_basicOpen s h hW hW' n g.1 g.2 _ inf_le_left)
  obtain ⟨y, hy⟩ := hU x
  obtain ⟨g, hgle, hgy⟩ := exists_basicOpen_le_chartToBase s h hW hW' y
  refine ⟨⟨g, hgle⟩, ?_, x.2⟩
  rw [basicOpen_eq_chartToBase_preimage s hW' g]
  change chartToBase s W' hW' x.1 ∈ s.base.basicOpen g
  rw [← hy, ← base_projInclusionMap s W W' h hW hW' y, chartToBase_projInclusion s h hW hW' y]
  exact hgy

/-- **Stacks Project, Tag 01NO.** The canonical comparison
`θ : r^* 𝒪_{Proj 𝒜(W')}(n) ⟶ 𝒪_{Proj 𝒜(W)}(n)` attached to an inclusion `W ≤ W'` of affine opens
of the base is an isomorphism, for every `n : ℤ`. -/
@[stacks 01NO "the canonical twist isomorphisms θ, for an arbitrary inclusion of affine opens of \
the base; their compatibility with the multiplication maps is not covered"]
theorem isIso_twistMap_gradedSectionRestriction {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (n : ℤ) :
    IsIso (twistMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') n) := by
  have hoi : IsOpenImmersion (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW')) :=
    isOpenImmersion_projInclusionMap s h hW hW'
  refine isIso_twistMap_of_bijective _ _ n fun V => ?_
  refine bijective_sectionsMap_gradedSectionRestriction s h hW hW' n _ fun x => ?_
  obtain ⟨y, -, hy⟩ := x.2
  exact ⟨y, (base_projInclusionMap s W W' h hW hW' y).symm.trans hy⟩

end Stacks.RelativeProj.Situation

end
