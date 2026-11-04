module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.BasicOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative `Proj`: the cartesian chart squares, and the glued scheme

Let `s` be a relative `Proj` situation: a scheme `s.base` carrying a quasi-coherent,
commutative, nonnegatively graded algebra over its structure sheaf. For affine opens `W ≤ W'` of
the base, `StacksFrontier/AlgebraicGeometry/RelativeProj/Charts/BasicOpen.lean` settles the case
where `W` is a *standard* open of `W'`: the comparison morphism of charts is then an open
immersion onto the part of the chart over `W'` lying above `W`. This file descends that to an
arbitrary affine `W ≤ W'`, which is the remaining content of Stacks tag 01NO, and then glues the
charts into the relative projective spectrum of tag 01NQ.

The descent is a covering argument. The standard opens `D(g)` of `W'` that are contained in `W`
cover `W`, each of them is also a standard open of `W`, and the comparison morphisms from their
charts are open immersions with known images both into the chart over `W` and into the chart over
`W'`. The chart over `W` is therefore covered by open subschemes on each of which the comparison
morphism is an open immersion, and the comparison morphism is injective because a point of the
chart over `W` is determined by its image in the chart over `W'` together with the member of the
covering it lies in.

## Main definitions

* `Stacks.RelativeProj.Situation.chartToBase` is the structure morphism of a chart to the base,
  rather than to the affine open it lies over. It is what the covering argument is phrased in.
* `Stacks.RelativeProj.Situation.chartData` is the local gluing datum
  `Stacks.RelativeProj.Data` of the situation, with both of its topological hypotheses
  discharged.
* `Stacks.RelativeProj.Situation.relativeProj` is the relative projective spectrum,
  `Stacks.RelativeProj.Situation.relativeProjToBase` its structure morphism and
  `Stacks.RelativeProj.Situation.relativeProjChart` its charts.

## Main results

* `Stacks.RelativeProj.Situation.projInclusionMap_comp` and
  `Stacks.RelativeProj.Situation.projInclusionMap_comp_projInclusionToOpen`: the comparison
  morphisms are functorial and are morphisms over the base.
* `Stacks.RelativeProj.Situation.isOpenImmersion_projInclusionMap`: the comparison morphism of
  charts is an open immersion.
* `Stacks.RelativeProj.Situation.opensRange_projInclusionMap`: its image is the part of the chart
  over `W'` lying over `W`.
* `Stacks.RelativeProj.Situation.projInclusion_isPullback`: the chart square is cartesian.
* `Stacks.RelativeProj.Situation.relativeProjChart_isPullback`: the chart over an affine open of
  the base is the part of the relative projective spectrum lying over it. This is the defining
  property of a relative projective spectrum.
* `Stacks.RelativeProj.Situation.relativeProjChart_transition`: the charts are compatible with
  the comparison morphisms.

## Implementation notes

`chartToBase` replaces the pair (chart structure morphism, inclusion of the affine open) by a
single morphism to the base, which turns every membership statement in the covering argument into
one of the form `chartToBase x ∈ W`; the identity
`Stacks.RelativeProj.Situation.projInclusionToOpen_preimage_opensRange` is what converts between
that form and the one `Stacks.RelativeProj.Data` asks for.

The open-immersion property is assembled with
`AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists`, which needs a covering of the source
by open immersions compatible with the morphism *and* injectivity of the morphism. Injectivity is
where the commuting square is used: two points with the same image have the same image in the
base, hence lie in the same member of the covering, where the morphism is injective because it is
an open immersion there.

The statements whose types mention `AlgebraicGeometry.Scheme.Hom.opensRange` carry the relevant
`AlgebraicGeometry.IsOpenImmersion` instance as a `letI` in the statement, since `opensRange` is
only defined for an open immersion.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomogeneousLocalization HomogeneousIdeal

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The comparison morphisms of charts are functorial in the inclusion of affine opens. -/
public theorem projInclusionMap_comp (U V W : s.base.Opens) (hUV : U ≤ V) (hVW : V ≤ W)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    projInclusionMap s U W (hUV.trans hVW) hU hW =
      projInclusionMap s U V hUV hU hV ≫ projInclusionMap s V W hVW hV hW := by
  rw [projInclusionMap, projInclusionMap, projInclusionMap, ← Proj.map_comp]
  exact Proj.map_congr (gradedSectionRestriction_comp s U V W hUV hVW) _ _

/-- The comparison morphism of charts is a morphism over the base. -/
public theorem projInclusionMap_comp_projInclusionToOpen (U V : s.base.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap s U V h hU hV ≫ projInclusionToOpen s V hV =
      projInclusionToOpen s U hU ≫ s.base.homOfLE h := by
  rw [projInclusionToOpen, projInclusionToOpen, projInclusionMap, Proj.map_toSpecZero_assoc,
    Category.assoc, Category.assoc,
    Stacks.RelativeProj.isoSpec_inv_homOfLE hU hV h, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  exact congrArg
    (fun k => Proj.toSpecZero (s.sectionRingGrading U) ≫ Spec.map k ≫ hV.isoSpec.inv)
    (sectionRingZeroMap_restrict s U V h).symm

/-- The structure morphism of the chart over an affine open, as a morphism to the base. -/
public noncomputable def chartToBase (U : s.base.Opens) (hU : IsAffineOpen U) :
    Proj (s.sectionRingGrading U) ⟶ s.base :=
  projInclusionToOpen s U hU ≫ U.ι

/-- The comparison morphism of charts commutes with the structure morphisms to the base. -/
public theorem projInclusionMap_comp_chartToBase (U V : s.base.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap s U V h hU hV ≫ chartToBase s V hV = chartToBase s U hU := by
  rw [chartToBase, chartToBase, ← Category.assoc, projInclusionMap_comp_projInclusionToOpen,
    Category.assoc, Scheme.homOfLE_ι]

/-- A chart lies over the affine open it is attached to. -/
public theorem chartToBase_mem (U : s.base.Opens) (hU : IsAffineOpen U)
    (x : Proj (s.sectionRingGrading U)) : chartToBase s U hU x ∈ U := by
  have hmem : chartToBase s U hU x ∈ U.ι.opensRange :=
    ⟨projInclusionToOpen s U hU x, (Scheme.Hom.comp_apply _ _ x).symm⟩
  rwa [U.opensRange_ι] at hmem

/-- The part of a chart lying over a smaller affine open, computed with the structure morphism to
the base instead of the one to the affine open. -/
public theorem projInclusionToOpen_preimage_opensRange (U V : s.base.Opens) (h : U ≤ V)
    (hV : IsAffineOpen V) :
    projInclusionToOpen s V hV ⁻¹ᵁ (s.base.homOfLE h).opensRange = chartToBase s V hV ⁻¹ᵁ U := by
  rw [Scheme.opensRange_homOfLE, chartToBase, Scheme.Hom.comp_preimage]

/-- The standard-open case of the open-immersion property, with the smaller open given by an
equation rather than as a standard open on the nose. -/
public theorem isOpenImmersion_projInclusionMap_of_eq_basicOpen {W W' : s.base.Opens}
    (hW' : IsAffineOpen W') (g : Γ(s.base, W')) (hWeq : W = s.base.basicOpen g)
    (h : W ≤ W') (hW : IsAffineOpen W) :
    IsOpenImmersion (projInclusionMap s W W' h hW hW') := by
  subst hWeq
  exact isOpenImmersion_projInclusionMap_basicOpen s g hW' hW

/-- The standard-open case of the image computation, in the `chartToBase` form. -/
public theorem opensRange_projInclusionMap_of_eq_basicOpen {W W' : s.base.Opens}
    (hW' : IsAffineOpen W') (g : Γ(s.base, W')) (hWeq : W = s.base.basicOpen g)
    (h : W ≤ W') (hW : IsAffineOpen W) :
    letI := isOpenImmersion_projInclusionMap_of_eq_basicOpen s hW' g hWeq h hW
    (projInclusionMap s W W' h hW hW').opensRange = chartToBase s W' hW' ⁻¹ᵁ W := by
  subst hWeq
  have := isOpenImmersion_projInclusionMap_basicOpen s g hW' hW
  rw [← projInclusionToOpen_preimage_opensRange s _ W' h hW']
  exact (opensRange_projInclusionMap_basicOpen s g hW' hW).symm


section Descent

/-- A standard open of `W'` contained in `W` is a standard open of `W`. -/
private theorem basicOpen_res_eq {W W' : s.base.Opens} (h : W ≤ W') (g : Γ(s.base, W'))
    (hg : s.base.basicOpen g ≤ W) :
    s.base.basicOpen (s.base.presheaf.map (homOfLE h).op g) = s.base.basicOpen g := by
  rw [Scheme.basicOpen_res, inf_eq_right.mpr hg]

/-- A point of the base lying in `W ≤ W'` lies in a standard open of `W'` contained in `W`. -/
private theorem exists_basicOpen_le_mem {W W' : s.base.Opens} (h : W ≤ W')
    (hW' : IsAffineOpen W') {p : s.base} (hp : p ∈ W) :
    ∃ g : Γ(s.base, W'), s.base.basicOpen g ≤ W ∧ p ∈ s.base.basicOpen g := by
  obtain ⟨g, hg, hpg⟩ := hW'.exists_basicOpen_le (⟨p, hp⟩ : W) (h hp)
  exact ⟨g, hg, hpg⟩

/-- The comparison morphism from the chart over a member of the covering into the chart over
`W` is an open immersion. -/
private theorem isOpenImmersion_smallChart {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (g : Γ(s.base, W'))
    (hg : s.base.basicOpen g ≤ W) :
    IsOpenImmersion (projInclusionMap s (s.base.basicOpen g) W hg (hW'.basicOpen g) hW) :=
  isOpenImmersion_projInclusionMap_of_eq_basicOpen s hW
    (s.base.presheaf.map (homOfLE h).op g) (basicOpen_res_eq s h g hg).symm hg (hW'.basicOpen g)

/-- Its image is the part of the chart over `W` lying over that member. -/
private theorem opensRange_smallChart {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (g : Γ(s.base, W'))
    (hg : s.base.basicOpen g ≤ W) :
    letI := isOpenImmersion_smallChart s h hW hW' g hg
    (projInclusionMap s (s.base.basicOpen g) W hg (hW'.basicOpen g) hW).opensRange =
      chartToBase s W hW ⁻¹ᵁ s.base.basicOpen g :=
  opensRange_projInclusionMap_of_eq_basicOpen s hW
    (s.base.presheaf.map (homOfLE h).op g) (basicOpen_res_eq s h g hg).symm hg (hW'.basicOpen g)

/-- The comparison morphism does not change the image of a point in the base. -/
private theorem chartToBase_projInclusionMap {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (z : Proj (s.sectionRingGrading W)) :
    chartToBase s W' hW' (projInclusionMap s W W' h hW hW' z) = chartToBase s W hW z := by
  rw [← Scheme.Hom.comp_apply, projInclusionMap_comp_chartToBase]

/-- The comparison morphism from the chart over a member of the covering into the chart over
`W'` is an open immersion. -/
private theorem isOpenImmersion_bigChart {W W' : s.base.Opens} (h : W ≤ W')
    (hW' : IsAffineOpen W') (g : Γ(s.base, W')) (hg : s.base.basicOpen g ≤ W) :
    IsOpenImmersion (projInclusionMap s (s.base.basicOpen g) W' (hg.trans h)
      (hW'.basicOpen g) hW') :=
  isOpenImmersion_projInclusionMap_of_eq_basicOpen s hW' g rfl (hg.trans h) (hW'.basicOpen g)

/-- That morphism factors through the chart over `W`. -/
private theorem bigChart_eq {W W' : s.base.Opens} (h : W ≤ W') (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (g : Γ(s.base, W')) (hg : s.base.basicOpen g ≤ W)
    (z : Proj (s.sectionRingGrading (s.base.basicOpen g))) :
    projInclusionMap s (s.base.basicOpen g) W' (hg.trans h) (hW'.basicOpen g) hW' z =
      projInclusionMap s W W' h hW hW'
        (projInclusionMap s (s.base.basicOpen g) W hg (hW'.basicOpen g) hW z) := by
  rw [projInclusionMap_comp s (s.base.basicOpen g) W W' hg h (hW'.basicOpen g) hW hW',
    Scheme.Hom.comp_apply]

/-- **The comparison morphism of charts is injective.** Two points with the same image have the
same image in the base, so they lie in the same member of the covering of the chart over `W` by
the charts over the standard opens of `W'` contained in `W`, where the morphism is injective. -/
private theorem injective_projInclusionMap {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') :
    Function.Injective (projInclusionMap s W W' h hW hW').base := by
  intro x y hxy
  obtain ⟨g, hgle, hgx⟩ := exists_basicOpen_le_mem s h hW' (chartToBase_mem s W hW x)
  have hoi := isOpenImmersion_smallChart s h hW hW' g hgle
  have hrange := opensRange_smallChart s h hW hW' g hgle
  have hoiq := isOpenImmersion_bigChart s h hW' g hgle
  have hyx : chartToBase s W hW y = chartToBase s W hW x := by
    rw [← chartToBase_projInclusionMap s h hW hW' y, ← chartToBase_projInclusionMap s h hW hW' x]
    exact congrArg (chartToBase s W' hW') hxy.symm
  obtain ⟨x', hx'eq⟩ : x ∈ (projInclusionMap s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW).opensRange := by rw [hrange]; exact hgx
  obtain ⟨y', hy'eq⟩ : y ∈ (projInclusionMap s (s.base.basicOpen g) W hgle
      (hW'.basicOpen g) hW).opensRange := by
    rw [hrange]
    exact (show chartToBase s W hW y ∈ _ from hyx ▸ hgx)
  have hxy' : x' = y' := by
    refine (projInclusionMap s (s.base.basicOpen g) W' (hgle.trans h) (hW'.basicOpen g)
      hW').isOpenEmbedding.injective ?_
    rw [bigChart_eq s h hW hW' g hgle x', bigChart_eq s h hW hW' g hgle y', hx'eq, hy'eq, hxy]
  rw [← hx'eq, ← hy'eq, hxy']

end Descent


/-- **Stacks Project, Tag 01NO.** The comparison morphism of charts attached to an inclusion of
affine opens of the base is an open immersion. -/
public theorem isOpenImmersion_projInclusionMap {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') :
    IsOpenImmersion (projInclusionMap s W W' h hW hW') := by
  refine IsOpenImmersion.of_forall_source_exists _ (injective_projInclusionMap s h hW hW') ?_
  intro x
  obtain ⟨g, hgle, hgx⟩ := exists_basicOpen_le_mem s h hW' (chartToBase_mem s W hW x)
  refine ⟨_, projInclusionMap s (s.base.basicOpen g) W hgle (hW'.basicOpen g) hW,
    isOpenImmersion_smallChart s h hW hW' g hgle, ?_, ?_⟩
  · rw [opensRange_smallChart s h hW hW' g hgle]
    exact hgx
  · rw [← projInclusionMap_comp s (s.base.basicOpen g) W W' hgle h (hW'.basicOpen g) hW hW']
    exact isOpenImmersion_bigChart s h hW' g hgle

/-- **Stacks Project, Tag 01NO.** The image of the comparison morphism of charts is the part of
the chart over the larger affine open that lies over the smaller one. -/
public theorem opensRange_projInclusionMap {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') :
    letI := isOpenImmersion_projInclusionMap s h hW hW'
    (projInclusionMap s W W' h hW hW').opensRange = chartToBase s W' hW' ⁻¹ᵁ W := by
  have hoi := isOpenImmersion_projInclusionMap s h hW hW'
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    show chartToBase s W' hW' (projInclusionMap s W W' h hW hW' x) ∈ W
    rw [chartToBase_projInclusionMap]
    exact chartToBase_mem s W hW x
  · intro z hz
    obtain ⟨g, hgle, hgz⟩ :=
      exists_basicOpen_le_mem s h hW' (show chartToBase s W' hW' z ∈ W from hz)
    have hoiq := isOpenImmersion_bigChart s h hW' g hgle
    have hrq : (projInclusionMap s (s.base.basicOpen g) W' (hgle.trans h)
        (hW'.basicOpen g) hW').opensRange = chartToBase s W' hW' ⁻¹ᵁ s.base.basicOpen g :=
      opensRange_projInclusionMap_of_eq_basicOpen s hW' g rfl (hgle.trans h) (hW'.basicOpen g)
    have hzq : z ∈ (projInclusionMap s (s.base.basicOpen g) W' (hgle.trans h)
        (hW'.basicOpen g) hW').opensRange := by
      rw [hrq]
      exact hgz
    obtain ⟨w, hw⟩ := hzq
    exact ⟨projInclusionMap s (s.base.basicOpen g) W hgle (hW'.basicOpen g) hW w,
      by rw [← bigChart_eq s h hW hW' g hgle w, hw]⟩


/-- The image of the comparison morphism, in the form the local gluing datum
`Stacks.RelativeProj.Data` asks for. -/
public theorem projInclusionToOpen_preimage_eq_opensRange {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') :
    letI := isOpenImmersion_projInclusionMap s h hW hW'
    projInclusionToOpen s W' hW' ⁻¹ᵁ (s.base.homOfLE h).opensRange =
      (projInclusionMap s W W' h hW hW').opensRange := by
  have hoi := isOpenImmersion_projInclusionMap s h hW hW'
  rw [projInclusionToOpen_preimage_opensRange s W W' h hW',
    opensRange_projInclusionMap s h hW hW']

/-- **Stacks Project, Tag 01NO.** The square formed by the comparison morphism of charts, the two
chart structure morphisms and the inclusion of affine opens of the base is cartesian. -/
@[stacks 01NO "the cartesian square"]
public theorem projInclusion_isPullback {W W' : s.base.Opens} (h : W ≤ W')
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') :
    IsPullback (projInclusionMap s W W' h hW hW') (projInclusionToOpen s W hW)
      (projInclusionToOpen s W' hW') (s.base.homOfLE h) :=
  projInclusion_isPullback_of s W W' h
    (fun {X Y} hXY => isOpenImmersion_projInclusionMap s hXY X.2 Y.2)
    (fun {X Y} hXY => projInclusionToOpen_preimage_eq_opensRange s hXY X.2 Y.2) hW hW'

/-- The charts of a situation, as the local gluing datum of a relative projective spectrum. Both
topological hypotheses of `Stacks.RelativeProj.Situation.localData` are now discharged. -/
public noncomputable def chartData :
    Data (fun W : s.base.affineOpens => s.sectionRingGrading W.1) :=
  localData s (fun {X Y} hXY => isOpenImmersion_projInclusionMap s hXY X.2 Y.2)
    (fun {X Y} hXY => projInclusionToOpen_preimage_eq_opensRange s hXY X.2 Y.2)


/-- **Stacks Project, Tag 01NQ.** The relative projective spectrum of a quasi-coherent
nonnegatively graded algebra on a scheme: the scheme glued from the projective spectra of the
graded rings of local sections over the affine opens of the base. -/
@[stacks 01NQ, ega "II 3.1.2", ega "II 8.3.1" "more general"]
public noncomputable def relativeProj : Scheme.{u} := (chartData s).relativeProj

/-- The structure morphism of the relative projective spectrum to its base. -/
@[stacks 01NQ]
public noncomputable def relativeProjToBase : relativeProj s ⟶ s.base := (chartData s).toBase

/-- The chart over an affine open of the base, as a morphism into the relative projective
spectrum. -/
@[stacks 01NQ]
public noncomputable def relativeProjChart (W : s.base.affineOpens) :
    Proj (s.sectionRingGrading W.1) ⟶ relativeProj s := (chartData s).chartι W

/-- **The chart over `W` is the part of the relative projective spectrum lying over `W`.** This
is the defining property of a relative projective spectrum. -/
@[stacks 01NQ]
public theorem relativeProjChart_isPullback (W : s.base.affineOpens) :
    IsPullback (relativeProjChart s W) (projInclusionToOpen s W.1 W.2)
      (relativeProjToBase s) W.1.ι :=
  ((chartData s).isPullback_chartι W).flip

/-- The charts are compatible with the comparison morphisms of charts. -/
@[stacks 01NQ]
public theorem relativeProjChart_transition {W W' : s.base.affineOpens} (h : W ≤ W') :
    projInclusionMap s W.1 W'.1 h W.2 W'.2 ≫ relativeProjChart s W' = relativeProjChart s W :=
  colimit.w (chartData s).gluingData.functor (homOfLE h)

end Stacks.RelativeProj.Situation
end
