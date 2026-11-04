module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.ComparisonComp
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleChartRefine
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback

/-!
# The chart-refinement law of the glueing of `𝒪_{Proj(s)}(n)`

Let `s` be a relative `Proj` situation, so that `Stacks.RelativeProj.Situation.twistSheaf` glues
the chart twists `Stacks.RelativeProj.Situation.twistChart` along the charts
`Stacks.RelativeProj.Situation.relativeProjChart`. For an inclusion `W ≤ W'` of affine opens of
the base the charts are related by `Stacks.RelativeProj.Situation.projInclusionMap`, an open
immersion, and the chart twists by the canonical comparison
`Stacks.ProjTwistComparison.twistMap` of the restriction of the graded section rings.

This file proves that those two relations agree with the chart identifications
`Stacks.RelativeProj.Situation.twistSheafChartIso` of the glued sheaf: **reading a section of
`𝒪(n)` on the larger chart and then comparing down is reading it on the smaller chart.** It is
the twist counterpart of
`Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap`, and the proof is the same one.

## Main results

* `Stacks.RelativeProj.Situation.twistSheafChartIso_hom_map_eqToHom`: reading a section of
  `𝒪(n)` over an open lying in a chart on that chart, with the two transports along the
  identification of the open with the image of its preimage cancelled.
* `Stacks.RelativeProj.Situation.restrictUnit_comp_twistSheafChartIso_twistPushforwardMap`: the
  identity as an equality of morphisms `𝒪(n) ⟶ (chart W)_* (twistChart s n W)`.
* `Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_twistMap`: **the chart-refinement law**,
  as the cocycle condition on the identifications of inverse images, which is the shape
  `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes.

The section-level identity this rests on is
`Stacks.RelativeProj.Situation.twistPushforwardMap_twistSectionsIso`, which is proved
with the construction of the transition datum.

## Implementation notes

The identity is proved on the other side of the pullback--pushforward adjunction, which is the
route `Stacks.ProjTwistComparison.twistMap_comp_of_eq` takes for the composition law. An inverse
image of a sheaf of modules is a sheafification of a tensor product and has no usable description
of its sections, so an identity of morphisms out of one cannot be checked on sections; its
transpose is a morphism into a direct image, whose sections over an open are the sections of its
argument over the preimage.

The three transposes involved are all explicit. The two chart identifications are identifications
of *restrictions* turned into identifications of inverse images by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso` computes the transpose of such a
thing. The middle one is `Stacks.ProjTwistComparison.transpose_twistMap`. The middle two factors
of the resulting identity are then the definition of
`Stacks.RelativeProj.Situation.twistPushforwardMap`, because
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id` makes the
pseudofunctoriality factor of the direct image the identity.

What is left is an identity of morphisms into a direct image along the chart over `W`, and such a
morphism is determined by its components over the opens inside the chart's range, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective` with
`Stacks.AlgebraicGeometry.Tag07ZGTwist.injective_pushforward_resLE`.

Three generic helpers of the module chain are reused rather than restated — the identification of
an open inside a chart with the image of its preimage, the thinness of the category of opens, and
the cancellation of two restrictions in opposite directions. They are
`public` where they stand.

## Not done here

No tag is claimed: this is a coherence law of a glueing, not a clause of a tag.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.RelativeProj.Situation

open Stacks.SheafOfModules

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (s : Situation.{u}) (n : ℤ)

/-! ### Reading a section of `𝒪(n)` through a chart -/

/-- **Reading a section of `𝒪(n)` over an open lying in a chart on that chart**: the chart
identification, applied to the section transported onto the image of the preimage, is the reading
given by the glueing datum. The two transports along the identification of an open inside a chart
with the image of its preimage cancel. -/
public theorem twistSheafChartIso_hom_map_eqToHom (W : s.base.affineOpens)
    {V₀ : (relativeProj s).Opens} (hV : V₀ ≤ (relativeProjChart s W).opensRange)
    (p : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (a : ToType ((twistSheaf s n).val.obj (op V₀))) :
    (((twistSheafChartIso s n W).hom.val.app (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
        (((twistSheaf s n).val.presheaf.map (eqToHom p).op) a))
      = (twistSectionsIso (twistTransition s n) W hV).hom a := by
  refine Eq.trans ((twistGlueData (twistTransition s n)).chartIso_hom_app W
    (relativeProjChart s W ⁻¹ᵁ V₀) _) ?_
  refine Eq.trans (congrArg _ (twistSectionsIso_restrict (twistTransition s n) W hV
    (le_of_eq p) a)) ?_
  have hself : ∀ {X : Scheme.{u}} (M : X.Modules) {U U' : X.Opens}
      (g₁ : (op U : (TopologicalSpace.Opens X)ᵒᵖ) ⟶ op U')
      (g₂ : (op U' : (TopologicalSpace.Opens X)ᵒᵖ) ⟶ op U) (w : ToType (M.val.obj (op U))),
      (M.val.presheaf.map g₂) ((M.val.presheaf.map g₁) w) = w := by
    intro X M U U' g₁ g₂ w
    obtain rfl : U = U' := le_antisymm (leOfHom g₂.unop) (leOfHom g₁.unop)
    obtain rfl : g₁ = 𝟙 _ := Subsingleton.elim _ _
    obtain rfl : g₂ = 𝟙 _ := Subsingleton.elim _ _
    simp
    rfl
  exact hself (twistChart s n W) _ _ _

/-- **Reading a section of `𝒪(n)` on the chart over `W`, over an open inside that chart.** This is
`Stacks.RelativeProj.Situation.twistSheafChartIso_hom_map_eqToHom` with the transport written as
the restriction map the unit of the restriction--direct-image adjunction uses, which is the
spelling the morphism-level statement below reduces to. -/
public theorem twistSheafChartIso_hom_map_homOfLE (W : s.base.affineOpens)
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (a : ToType ((twistSheaf s n).val.obj (op V))) :
    ((twistSheafChartIso s n W).hom.val.app (op (relativeProjChart s W ⁻¹ᵁ V))).hom
        (((twistSheaf s n).val.presheaf.map
          (homOfLE ((relativeProjChart s W).image_preimage_le V)).op) a)
      = (twistSectionsIso (twistTransition s n) W hV).hom a := by
  have hthin : ∀ {X : Scheme.{u}} (M : X.Modules) {A B : X.Opens} (hle : A ≤ B) (he : A = B)
      (a : ToType (M.val.obj (op B))),
      ((M.val.presheaf.map (homOfLE hle).op) a) = ((M.val.presheaf.map (eqToHom he).op) a) :=
    fun M _ _ _ _ a => congrArg (fun k => (M.val.presheaf.map (Quiver.Hom.op k)) a)
      (Subsingleton.elim _ _)
  have hV' : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V) = V :=
    Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self (relativeProjChart s W)
      (hV.trans_eq (Scheme.Hom.image_top_eq_opensRange (relativeProjChart s W)).symm)
  exact (congrArg (fun z => ((twistSheafChartIso s n W).hom.val.app
        (op (relativeProjChart s W ⁻¹ᵁ V))).hom z)
    (hthin (twistSheaf s n) ((relativeProjChart s W).image_preimage_le V) hV' a)).trans
    (twistSheafChartIso_hom_map_eqToHom s n W hV hV' a)

/-- **The chart-refinement law of the glueing of `𝒪(n)`, as an identity of morphisms into a direct
image.** Reading a section of `𝒪(n)` on the chart over the larger affine open `W'` and then
comparing the chart twists down to `W` is reading it on the chart over `W`.

Both sides are morphisms `𝒪(n) ⟶ (chart W)_* (twistChart s n W)`, and such a morphism is
determined by its components over the opens inside the range of the chart over `W`, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective`. Over such an open the identity
is `Stacks.RelativeProj.Situation.twistPushforwardMap_twistSectionsIso`. -/
public theorem restrictUnit_comp_twistSheafChartIso_twistPushforwardMap
    {W W' : s.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.restrictAdjunction (relativeProjChart s W')).unit.app (twistSheaf s n)
        ≫ (Scheme.Modules.pushforward (relativeProjChart s W')).map
            (twistSheafChartIso s n W').hom
        ≫ twistPushforwardMap s n h
      = (Scheme.Modules.restrictAdjunction (relativeProjChart s W)).unit.app (twistSheaf s n)
        ≫ (Scheme.Modules.pushforward (relativeProjChart s W)).map
            (twistSheafChartIso s n W).hom := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective
    (W₀ := (relativeProjChart s W).opensRange) (fun V => ?_) (fun V hVle a => ?_)
  · refine Stacks.AlgebraicGeometry.Tag07ZGTwist.injective_pushforward_resLE
      (relativeProjChart s W) (twistChart s n W) inf_le_left ?_
    refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x, rfl⟩⟩
  · exact (congrArg (fun z => ((twistPushforwardMap s n h).val.app (op V)).hom z)
        (twistSheafChartIso_hom_map_homOfLE s n W'
          (hVle.trans (opensRange_relativeProjChart_mono s h)) a)).trans
      ((twistPushforwardMap_twistSectionsIso s n h hVle a).trans
        (twistSheafChartIso_hom_map_homOfLE s n W hVle a).symm)

/-! ### The chart-refinement law on inverse images -/

variable {W W' : s.base.affineOpens} (h : W ≤ W')

/-- The comparison of the pushed-forward chart twists without its pseudofunctoriality factor,
which is the identity by
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id`. This is the shape in
which the tail of `Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` presents it. -/
public theorem twistPushforwardMap_eq_pushforwardTwistMap_comp :
    twistPushforwardMap s n h
      = (Scheme.Modules.pushforward (relativeProjChart s W')).map
            (Stacks.ProjTwistComparison.pushforwardTwistMap
              (gradedSectionRestriction s W.1 W'.1 h)
              (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n)
        ≫ (Scheme.Modules.pushforwardCongr (relativeProjChart_transition s h)).hom.app
            (twistChart s n W) :=
  (whisker_eq _ (eq_whisker
      (Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id
        (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W')
        (twistChart s n W)) _)).trans
    (whisker_eq _ (Category.id_comp _))

/-- **The chart-refinement law of the glueing of `𝒪(n)`.** For an inclusion `W ≤ W'` of affine
opens of the base, the identification of `(chart W)^* 𝒪(n)` with the inverse image along
`Stacks.RelativeProj.Situation.projInclusionMap` of the chart twist over `W'`, followed by the
canonical comparison `Stacks.ProjTwistComparison.twistMap` of the chart twists, is the
identification of `(chart W)^* 𝒪(n)` with the chart twist over `W`.

This is the cocycle shape that
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes, written
with the identification of the inverse image along the composite spelled out as the congruence
and pseudofunctoriality comparisons — exactly as
`Stacks.ProjTwistComparison.twistMap_comp_of_eq` is. -/
public theorem pullbackCongr_inv_comp_twistMap :
    (Scheme.Modules.pullbackCongr (relativeProjChart_transition s h)).inv.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackComp (projInclusionMap s W.1 W'.1 h W.2 W'.2)
            (relativeProjChart s W')).inv.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullback (projInclusionMap s W.1 W'.1 h W.2 W'.2)).map
            (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
              (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').hom
        ≫ Stacks.ProjTwistComparison.twistMap (gradedSectionRestriction s W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W)).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W).hom := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective _ _ ?_
  refine ((Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle
    (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W') (relativeProjChart s W)
    (relativeProjChart_transition s h) (twistSheaf s n) (twistChart s n W') (twistChart s n W)
    _ _ _ rfl).symm).trans ?_
  refine Eq.trans (eq_whisker (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso
    (relativeProjChart s W') (twistSheaf s n) (twistChart s n W')
    (twistSheafChartIso s n W')) _) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward (relativeProjChart s W')).map z)
    (Stacks.ProjTwistComparison.transpose_twistMap (gradedSectionRestriction s W.1 W'.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n)) _)) ?_
  refine Eq.trans (whisker_eq _
    (twistPushforwardMap_eq_pushforwardTwistMap_comp s n h).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (restrictUnit_comp_twistSheafChartIso_twistPushforwardMap s n h) ?_
  exact (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso
    (relativeProjChart s W) (twistSheaf s n) (twistChart s n W)
    (twistSheafChartIso s n W)).symm

end Stacks.RelativeProj.Situation

end
