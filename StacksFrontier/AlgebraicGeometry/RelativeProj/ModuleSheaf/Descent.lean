module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.BasicOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Local
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Descent

/-!
# Descent of the module comparison to a general affine open

In a relative `Proj` situation, let `ℳ` be a graded module over its graded algebra whose
homogeneous pieces are quasi-coherent, let `W ≤ W'` be affine opens of the base and let
`r : Proj 𝒜(W) ⟶ Proj 𝒜(W')` be the comparison morphism of charts. This file proves that the
comparison of the sheaves attached to the graded modules of local sections of `ℳ` on the two
charts is bijective on sections over every open of `Proj 𝒜(W')` whose points come from
`Proj 𝒜(W)`.

`Stacks.ProjModuleComparison.bijective_sectionsMap` settles the case where the graded restriction
map is a degreewise localization away from a degree-zero element, which by
`Stacks.RelativeProj.Situation.isAwayDegreewiseModule_basicOpen` is the case where `W` is a
*standard* open `D(g)` of `W'`. For a general affine open `W`, the standard opens `D(g)` of `W'`
contained in `W` cover `W`, and each of them is also a standard open of `W`, so the restriction
`ℳ(W') → ℳ(D(g))` factors as `ℳ(W') → ℳ(W) → ℳ(D(g))` with both the composite and the second
factor degreewise localizations.

## Main results

* `Stacks.RelativeProj.Situation.bijective_fibreMap_sectionModuleRestrict`: the module fibre
  comparison of the restriction of the graded modules of sections is bijective at every point of
  the smaller chart.
* `Stacks.RelativeProj.Situation.bijective_sectionsMap_sectionModuleRestrict`: **the comparison
  on sections of the sheaves attached to `ℳ` on two charts is bijective** over every open of the
  chart over `W'` lying in the image of the chart over `W`.

## Implementation notes

The element of `𝒜(W)₀` that the restriction to `D(g)` is a degreewise localization away from is
written as the image of `s.sectionRingBaseMap W' g` under the restriction `𝒜(W') → 𝒜(W)`, rather
than as `s.sectionRingBaseMap W` of the restricted section, exactly as in the ring case: the two
agree by `Stacks.RelativeProj.Situation.gradedSectionRestriction_baseMap`, but the first form is
the one in which non-vanishing at a point of `Proj 𝒜(W)` is read off from non-vanishing at its
image in `Proj 𝒜(W')`, with no rewriting under the homogeneous ideal.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. The morphism `r^* ℳ̃(W') ⟶ ℳ̃(W)` is not shown to be an isomorphism —
only its adjoint transpose is shown bijective on the sections that a glueing consumes — and
nothing is glued: the sheaf `ℳ̃` on the relative `Proj` is not constructed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjModuleComparison Stacks.GradedLocalization
open scoped Stacks.GradedLocalization

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)

/-- Restriction of the graded modules of local sections preserves the internal grading. -/
public theorem sectionModuleRestrictₛₗ_mem_grading {U V : s.base.Opens} (h : U ≤ V) (i : ℤ)
    {z : sectionModule ℳ V} (hz : z ∈ sectionModuleGrading ℳ V i) :
    sectionModuleRestrictₛₗ ℳ h z ∈ sectionModuleGrading ℳ U i :=
  sectionModuleRestrict_mem_grading ℳ h hz

/-- **Restriction of the graded modules of local sections is functorial**, read at a section:
the pointwise form of `Stacks.RelativeProj.Situation.sectionModuleRestrict_comp`. -/
public theorem sectionModuleRestrictₛₗ_trans {U V W : s.base.Opens} (hUV : U ≤ V) (hVW : V ≤ W)
    (z : sectionModule ℳ W) :
    sectionModuleRestrictₛₗ ℳ (hUV.trans hVW) z
      = sectionModuleRestrictₛₗ ℳ hUV (sectionModuleRestrictₛₗ ℳ hVW z) := by
  rw [sectionModuleRestrictₛₗ_apply, sectionModuleRestrictₛₗ_apply,
    sectionModuleRestrictₛₗ_apply, sectionModuleRestrict_comp ℳ hUV hVW]
  rfl

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-! ### The two degreewise localizations attached to a standard open -/

/-- The restriction of the graded modules of local sections to an affine open presented as a
standard open by an equation is a degreewise localization. -/
private theorem isAwayDegreewiseModule_of_eq_basicOpen {W W' : s.base.Opens}
    (hW' : IsAffineOpen W') (g : Γ(s.base, W')) (hWeq : W = s.base.basicOpen g) (hle : W ≤ W') :
    IsAwayDegreewiseModule (gradedSectionRestriction s W W' hle)
      (sectionModuleGrading ℳ W') (sectionModuleGrading ℳ W)
      (sectionModuleRestrictₛₗ ℳ hle) (s.sectionRingBaseMap W' g) := by
  subst hWeq
  exact isAwayDegreewiseModule_basicOpen ℳ g hW'

/-- **The restriction `ℳ(W) → ℳ(D(g))` is a degreewise localization away from the image of `g`**,
for a standard open `D(g)` of `W'` contained in `W`. -/
private theorem isAwayDegreewiseModule_restrictOfBase {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (g : Γ(s.base, W')) (hgle : s.base.basicOpen g ≤ W) :
    IsAwayDegreewiseModule (gradedSectionRestriction s (s.base.basicOpen g) W hgle)
      (sectionModuleGrading ℳ W) (sectionModuleGrading ℳ (s.base.basicOpen g))
      (sectionModuleRestrictₛₗ ℳ hgle)
      ((gradedSectionRestriction s W W' h) (s.sectionRingBaseMap W' g)) := by
  rw [gradedSectionRestriction_baseMap' s h g]
  refine isAwayDegreewiseModule_of_eq_basicOpen ℳ hW
    (s.base.presheaf.map (homOfLE h).op g) ?_ hgle
  rw [Scheme.basicOpen_res, inf_eq_right.mpr hgle]

/-! ### The descent -/

/-- **The module fibre comparison of the restriction of the graded modules of sections is
bijective** at every point of the chart over `W`. -/
public theorem bijective_fibreMap_sectionModuleRestrict {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W)) :
    Function.Bijective (fibreMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW')
      (sectionModuleRestrictₛₗ ℳ h) y) := by
  obtain ⟨g, hgle, z, hz⟩ := exists_chart_point s h hW hW' y
  subst hz
  refine bijective_fibreMap_of_eq_comp _
    (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') _
    _ (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW) _
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W' (hgle.trans h)
      (hW'.basicOpen g) hW')
    (gradedSectionRestriction_comp s (s.base.basicOpen g) W W' hgle h)
    _ (sectionModuleRestrictₛₗ_trans ℳ hgle h) z ?_ ?_
  · exact bijective_fibreMap _ _ _ (isAwayDegreewise_basicOpen s g hW')
      (isAwayDegreewiseModule_basicOpen ℳ g hW') z
  · exact injective_localizedModuleMap _ _ _ _ (isAwayDegreewise_restrictOfBase s h hW g hgle)
      (isAwayDegreewiseModule_restrictOfBase ℳ h hW g hgle) rfl

/-- **The comparison on sections of `ℳ(W') → ℳ(W)` is surjective over an open of the chart over
`W'` where `g` does not vanish**, for a section `g` over `W'` with `D(g) ≤ W`. -/
private theorem surjective_sectionsMap_of_basicOpen {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (g : Γ(s.base, W'))
    (hgle : s.base.basicOpen g ≤ W)
    (V : Opens (ProjectiveSpectrum.top (s.sectionRingGrading W')))
    (hV : V ≤ AlgebraicGeometry.Proj.basicOpen (s.sectionRingGrading W')
      (s.sectionRingBaseMap W' g)) :
    Function.Surjective (sectionsMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW')
      (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h) V) := by
  have hx : ∀ x : V, s.sectionRingBaseMap W' g ∉ x.1.asHomogeneousIdeal := fun x =>
    (AlgebraicGeometry.Proj.mem_basicOpen (s.sectionRingGrading W')
      (s.sectionRingBaseMap W' g) x.1).mp (hV x.2)
  refine surjective_sectionsMap_of_eq_comp _
    (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') _
    (sectionModuleRestrictₛₗ_mem_grading ℳ h) _
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW)
    _ (sectionModuleRestrictₛₗ_mem_grading ℳ hgle)
    (irrelevant_le_map_gradedSectionRestriction s (s.base.basicOpen g) W' (hgle.trans h)
      (hW'.basicOpen g) hW')
    (gradedSectionRestriction_comp s (s.base.basicOpen g) W W' hgle h) _
    (sectionModuleRestrictₛₗ_mem_grading ℳ (hgle.trans h))
    (sectionModuleRestrictₛₗ_trans ℳ hgle h) V ?_ ?_
  · exact (bijective_sectionsMap _ _ _ _ (isAwayDegreewise_basicOpen s g hW')
      (sectionRingBaseMap_mem_zero s W' g)
      (isAwayDegreewiseModule_basicOpen ℳ g hW') V hx).2
  · exact injective_sectionsMap _ _ _ _ (isAwayDegreewise_restrictOfBase s h hW g hgle)
      ((gradedSectionRestriction s W W' h).map_mem (sectionRingBaseMap_mem_zero s W' g))
      (isAwayDegreewiseModule_restrictOfBase ℳ h hW g hgle) _ fun x => hx ⟨_, x.2⟩

/-- **The comparison on sections of the sheaves attached to `ℳ` on two charts is bijective** over
every open of the chart over `W'` whose points come from the chart over `W`. -/
public theorem bijective_sectionsMap_sectionModuleRestrict {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (U : Opens (ProjectiveSpectrum.top (s.sectionRingGrading W')))
    (hU : ∀ x : U, ∃ y : ProjectiveSpectrum (s.sectionRingGrading W),
      ProjectiveSpectrum.comapFun (gradedSectionRestriction s W W' h)
        (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW') y = x.1) :
    Function.Bijective (sectionsMap (gradedSectionRestriction s W W' h)
      (irrelevant_le_map_gradedSectionRestriction s W W' h hW hW')
      (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h) U) := by
  refine bijective_sectionsMap_of_cover _ _ _ _ U
    (ι := {g : Γ(s.base, W') // s.base.basicOpen g ≤ W})
    (fun g => AlgebraicGeometry.Proj.basicOpen (s.sectionRingGrading W')
      (s.sectionRingBaseMap W' g.1) ⊓ U)
    (fun _ => inf_le_right) (fun x => ?_) hU
    (fun y => (bijective_fibreMap_sectionModuleRestrict ℳ h hW hW' y).1)
    (fun g => surjective_sectionsMap_of_basicOpen ℳ h hW hW' g.1 g.2 _ inf_le_left)
  obtain ⟨y, hy⟩ := hU x
  have hyW : chartToBase s W hW y ∈ W := chartToBase_mem s W hW y
  obtain ⟨g, hgle, hgy⟩ := hW'.exists_basicOpen_le (⟨chartToBase s W hW y, hyW⟩ : W) (h hyW)
  refine ⟨⟨g, hgle⟩, ?_, x.2⟩
  rw [basicOpen_eq_chartToBase_preimage s hW' g]
  show chartToBase s W' hW' x.1 ∈ s.base.basicOpen g
  rw [← hy, ← base_projInclusionMap s W W' h hW hW' y, chartToBase_projInclusion s h hW hW' y]
  exact hgy

end Stacks.RelativeProj.Situation

end
