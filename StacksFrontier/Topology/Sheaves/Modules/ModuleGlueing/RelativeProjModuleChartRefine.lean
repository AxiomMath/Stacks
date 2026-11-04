module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.PushforwardCocycle
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonComp
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorGlueHom
public import StacksFrontier.AlgebraicGeometry.TwistUnique.Basic
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback

/-!
# The chart-refinement law of the glueing of `ℳ̃`

Let `s` be a relative `Proj` situation and `ℳ` a graded module over its graded algebra with
quasi-coherent homogeneous pieces, so that `Stacks.RelativeProj.Situation.moduleSheaf` glues the
chart sheaves `Stacks.RelativeProj.Situation.moduleChart` along the charts
`Stacks.RelativeProj.Situation.relativeProjChart`. For an inclusion `W ≤ W'` of affine opens of
the base the charts are related by `Stacks.RelativeProj.Situation.projInclusionMap`, an open
immersion, and the chart sheaves by the canonical comparison
`Stacks.ProjModuleComparison.moduleMap` of the restriction of the graded modules of sections.

This file proves that those two relations agree with the chart identifications
`Stacks.RelativeProj.Situation.moduleSheafChartIso` of the glued sheaf: **reading a section of
`ℳ̃` on the larger chart and then comparing down is reading it on the smaller chart.** The
identity is stated three times, in the three shapes its consumers take — on sections, as an
identity of morphisms into a direct image, and as the cocycle condition relating the inverse
images.

## Main results

* `Stacks.RelativeProj.Situation.restrictUnit_comp_moduleSheafChartIso_modulePushforwardMap`: the
  identity as an equality of morphisms `ℳ̃ ⟶ (chart W)_* (moduleChart ℳ W)`.
* `Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap`: **the chart-refinement law**,
  as the cocycle condition on the identifications of inverse images, which is the shape
  `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes.

The section-level identity this rests on is
`Stacks.RelativeProj.Situation.modulePushforwardMap_chartSectionsIso` of
`StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorGlueChart.lean`, proved together
with property (6).

## Implementation notes

The identity is proved on the other side of the pullback--pushforward adjunction, which is the
route `Stacks.ProjModuleComparison.moduleMap_comp_of_eq` takes for the composition law of the
comparisons. An inverse image of a sheaf of modules is a sheafification of a tensor product and
has no usable description of its sections, so an identity of morphisms out of one cannot be
checked on sections; its transpose is a morphism into a direct image, whose sections over an open
are the sections of its argument over the preimage.

The three transposes involved are all explicit. The two chart identifications are identifications
of *restrictions* turned into identifications of inverse images by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso` computes the transpose of such a
thing as the unit of the restriction--direct-image adjunction followed by the direct image of the
identification, with no inverse image left. The middle one is
`Stacks.ProjModuleComparison.transpose_moduleMap`, the comparison on sections. The middle two
factors of the resulting identity are then the definition of
`Stacks.RelativeProj.Situation.modulePushforwardMap`, because
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id` makes the
pseudofunctoriality factor of the direct image the identity.

What is left is an identity of morphisms into a direct image along the chart over `W`, and such a
morphism is determined by its components over the opens inside the chart's range, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective` with
`Stacks.AlgebraicGeometry.Tag07ZGTwist.injective_pushforward_resLE`. Over such an open the two
sides are the two chart readings of a section of `ℳ̃`, and those are compared by
`Stacks.SheafOfModules.ModulesGlueData.trans_chartSectionsIso` through the pairwise transition;
`Stacks.SheafOfModules.ModulesDirectedGlueData.pairTrans_eq_trans_symm` makes that transition the
nested one and `Stacks.RelativeProj.Situation.modulePushforwardMap_moduleTransEquiv` identifies it
with `modulePushforwardMap`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
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
attribute [local instance] sectionModuleDecomposition

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-! ### Reading a section of `ℳ̃` through a chart, as a morphism into a direct image -/

/-- An open inside the chart over an affine open of the base is the image of its own preimage. -/
private theorem image_preimage_relativeProjChart_eq (W : s.base.affineOpens)
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange) :
    relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V) = V :=
  Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self (relativeProjChart s W)
    (hV.trans_eq (Scheme.Hom.image_top_eq_opensRange (relativeProjChart s W)).symm)

/-- **Restriction of sections along an inclusion of opens which is an equality does not depend on
which of the two it is read as.** The category of opens is thin, so `homOfLE` and `eqToHom` of the
same pair of opens are the same morphism. Stated on bare variables: resolving the thinness of the
opens of a relative projective spectrum inside a statement about one exhausts the heartbeat
budget. -/
private theorem presheaf_map_homOfLE_eq_eqToHom {X : Scheme.{u}} (M : X.Modules)
    {A B : X.Opens} (hle : A ≤ B) (he : A = B) (a : ToType (M.val.obj (op B))) :
    ((M.val.presheaf.map (homOfLE hle).op) a) = ((M.val.presheaf.map (eqToHom he).op) a) :=
  congrArg (fun k : A ⟶ B => (M.val.presheaf.map k.op) a) (Subsingleton.elim _ _)

/-- **Reading a section of `ℳ̃` on the chart over `W`, over an open inside that chart.** This is
`Stacks.RelativeProj.Situation.moduleSheafChartIso_hom_map_eqToHom` with the transport written as
the restriction map the unit of the restriction--direct-image adjunction uses, which is the
spelling the morphism-level statement below reduces to. -/
private theorem moduleSheafChartIso_hom_map_homOfLE (W : s.base.affineOpens)
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (a : ToType ((moduleSheaf ℳ).val.obj (op V))) :
    ((moduleSheafChartIso ℳ W).hom.val.app (op (relativeProjChart s W ⁻¹ᵁ V))).hom
        (((moduleSheaf ℳ).val.presheaf.map
          (homOfLE ((relativeProjChart s W).image_preimage_le V)).op) a)
      = ((modulesDirectedGlueData ℳ).chartSectionsIso W hV).hom a :=
  (congrArg (fun z => ((moduleSheafChartIso ℳ W).hom.val.app
        (op (relativeProjChart s W ⁻¹ᵁ V))).hom z)
    (presheaf_map_homOfLE_eq_eqToHom (moduleSheaf ℳ)
      ((relativeProjChart s W).image_preimage_le V)
      (image_preimage_relativeProjChart_eq W hV) a)).trans
  (moduleSheafChartIso_hom_map_eqToHom ℳ W hV (image_preimage_relativeProjChart_eq W hV) a)

/-- **The chart-refinement law of the glueing of `ℳ̃`, as an identity of morphisms into a direct
image.** Reading a section of `ℳ̃` on the chart over the larger affine open `W'` and then
comparing the chart sheaves down to `W` is reading it on the chart over `W`.

Both sides are morphisms `ℳ̃ ⟶ (chart W)_* (moduleChart ℳ W)`, and such a morphism is determined
by its components over the opens inside the range of the chart over `W`, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective`: the restriction maps of the
direct image between an open and its intersection with the chart's range have the same preimage,
so they are injective by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.injective_pushforward_resLE`. Over such an open the
identity is `Stacks.RelativeProj.Situation.modulePushforwardMap_chartSectionsIso`. -/
public theorem restrictUnit_comp_moduleSheafChartIso_modulePushforwardMap
    {W W' : s.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.restrictAdjunction (relativeProjChart s W')).unit.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pushforward (relativeProjChart s W')).map
            (moduleSheafChartIso ℳ W').hom
        ≫ modulePushforwardMap ℳ h
      = (Scheme.Modules.restrictAdjunction (relativeProjChart s W)).unit.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pushforward (relativeProjChart s W)).map
            (moduleSheafChartIso ℳ W).hom := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective
    (W₀ := (relativeProjChart s W).opensRange) (fun V => ?_) (fun V hVle a => ?_)
  · refine Stacks.AlgebraicGeometry.Tag07ZGTwist.injective_pushforward_resLE
      (relativeProjChart s W) (moduleChart ℳ W) inf_le_left ?_
    refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x, rfl⟩⟩
  · exact (congrArg (fun z => ((modulePushforwardMap ℳ h).val.app (op V)).hom z)
        (moduleSheafChartIso_hom_map_homOfLE ℳ W'
          (hVle.trans (opensRange_relativeProjChart_mono s h)) a)).trans
      ((modulePushforwardMap_chartSectionsIso ℳ h hVle a).trans
        (moduleSheafChartIso_hom_map_homOfLE ℳ W hVle a).symm)

/-! ### The chart-refinement law on inverse images -/

variable {W W' : s.base.affineOpens} (h : W ≤ W')

omit [∀ (n : ℤ), (ℳ.piece n).IsQuasicoherent] in
/-- The comparison of the pushed-forward chart sheaves without its pseudofunctoriality factor,
which is the identity by
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id`. This is the shape in
which the tail of `Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` presents it. -/
private theorem modulePushforwardMap_eq_pushforwardModuleMap_comp :
    modulePushforwardMap ℳ h
      = (Scheme.Modules.pushforward (relativeProjChart s W')).map
            (Stacks.ProjModuleComparison.pushforwardModuleMap
              (gradedSectionRestriction s W.1 W'.1 h)
              (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
              (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h))
        ≫ (Scheme.Modules.pushforwardCongr (relativeProjChart_transition s h)).hom.app
            (moduleChart ℳ W) :=
  (whisker_eq _ (eq_whisker
      (Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id
        (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W')
        (moduleChart ℳ W)) _)).trans
    (whisker_eq _ (Category.id_comp _))

/-- **The chart-refinement law of the glueing of `ℳ̃`.** For an inclusion `W ≤ W'` of affine
opens of the base, the identification of `(chart W)^* ℳ̃` with the inverse image along
`Stacks.RelativeProj.Situation.projInclusionMap` of the chart sheaf over `W'`, followed by the
canonical comparison `Stacks.ProjModuleComparison.moduleMap` of the chart sheaves, is the
identification of `(chart W)^* ℳ̃` with the chart sheaf over `W`.

This is the cocycle shape that
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` consumes, written
with the identification of the inverse image along the composite spelled out as the congruence
and pseudofunctoriality comparisons — exactly as
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq` is.

It is proved on the other side of the adjunction. The three transposes are
`Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso` twice and
`Stacks.ProjModuleComparison.transpose_moduleMap` in the middle, and the resulting identity is
`Stacks.RelativeProj.Situation.restrictUnit_comp_moduleSheafChartIso_modulePushforwardMap`. -/
public theorem pullbackCongr_inv_comp_moduleMap :
    (Scheme.Modules.pullbackCongr (relativeProjChart_transition s h)).inv.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullbackComp (projInclusionMap s W.1 W'.1 h W.2 W'.2)
            (relativeProjChart s W')).inv.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullback (projInclusionMap s W.1 W'.1 h W.2 W'.2)).map
            (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
              (moduleSheaf ℳ)).symm ≪≫ moduleSheafChartIso ℳ W').hom
        ≫ Stacks.ProjModuleComparison.moduleMap (gradedSectionRestriction s W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
            (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h)
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W)).app
            (moduleSheaf ℳ)).symm ≪≫ moduleSheafChartIso ℳ W).hom := by
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_injective _ _ ?_
  refine ((Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle
    (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W') (relativeProjChart s W)
    (relativeProjChart_transition s h) (moduleSheaf ℳ) (moduleChart ℳ W') (moduleChart ℳ W)
    _ _ _ rfl).symm).trans ?_
  refine Eq.trans (eq_whisker (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso
    (relativeProjChart s W') (moduleSheaf ℳ) (moduleChart ℳ W') (moduleSheafChartIso ℳ W')) _) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward (relativeProjChart s W')).map z)
    (Stacks.ProjModuleComparison.transpose_moduleMap (gradedSectionRestriction s W.1 W'.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
      (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h))) _)) ?_
  refine Eq.trans (whisker_eq _
    (modulePushforwardMap_eq_pushforwardModuleMap_comp ℳ h).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (restrictUnit_comp_moduleSheafChartIso_modulePushforwardMap ℳ h) ?_
  exact (Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso
    (relativeProjChart s W) (moduleSheaf ℳ) (moduleChart ℳ W) (moduleSheafChartIso ℳ W)).symm

end Stacks.RelativeProj.Situation

end
