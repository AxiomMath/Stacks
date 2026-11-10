module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.ComparisonChart
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistChartRefine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisting sheaves of a relative `Proj` base change, glued

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback along `g` of that of `s` isomorphically in
every nonnegative degree, and let `r = relativeProjBaseChange g Φ hΦ`.
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjTwistBaseChange.lean` builds the
chart components of the degree-`n` part of Tag 01O3's `θ`, one for each index of the base-change
cover of `Proj_{S'}(𝒜')`. This file glues them into a morphism

`r^* 𝒪_{Proj_S(𝒜)}(n) ⟶ 𝒪_{Proj_{S'}(𝒜')}(n)`

on all of `Proj_{S'}(𝒜')`, and proves it is an isomorphism.

## The route

`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` asks for the agreement
of two chart components over the overlap of their charts, for an **arbitrary** pair of indices. The
cover combinatorics that reduces this to a *nested* pair is already available and is stated with no
reference to the sheaves involved: `Stacks.RelativeProj.Situation.iSup_image_top_baseChangeCover`
and `localApp_baseChangeCover_eq_of_nested`. So all that is needed is the nested case, and the
index is a pair, so that splits along its two components:

* the affine open of `S` shrinks — `twistChartBaseChangeHom_comp_eq_of_target_le`, which is
  `Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc` for the two charts of `S`, with the
  chart-refinement law of the glueing of `𝒪(n)` as its hypothesis;
* the affine open of `S'` shrinks — `twistSheafBaseChangePullbackHom_source_le`, which is
  `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq` at this situation.

A nested pair of indices factors through the index with the smaller open of `S'` and the larger
open of `S`, so the two compose to the nested case.

Invertibility is then local: the chart components are isomorphisms by
`Stacks.RelativeProj.Situation.isIso_twistSheafBaseChangeRestrictHom`, and a morphism of sheaves of
modules whose restrictions along a jointly surjective family of open immersions are isomorphisms
is one, by `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`.

## Main definitions

* `Stacks.RelativeProj.Situation.twistSheafBaseChangePullbackHom`: the chart component as a
  morphism of **inverse images** along the chart, rather than of the restrictions.
* `Stacks.RelativeProj.Situation.twistSheafBaseChangeHom`: the glued comparison
  `r^* 𝒪(n) ⟶ 𝒪'(n)`.
* `Stacks.RelativeProj.Situation.twistSheafPullbackIso`: **the twist assertion of Tag 01O3** —
  `θ n : r^* 𝒪_{Proj_S(𝒜)}(n) ≅ 𝒪_{Proj_{S'}(𝒜')}(n)`, in every degree.
* `Stacks.RelativeProj.Situation.twistSheafFibreProductIso`: the same read on the fibre product
  `S' ×_S Proj_S(𝒜)`, which is the shape the tag states.

## Main results

* `Stacks.RelativeProj.Situation.twistChartBaseChangeHom_comp_eq_of_target_le` and
  `twistSheafBaseChangePullbackHom_source_le`: the two halves of the nested case.
* `Stacks.RelativeProj.Situation.localApp_twistSheafBaseChangeRestrictHom_eq_of_nested`: the
  glueing compatibility over a nested pair of indices.
* `Stacks.RelativeProj.Situation.existsUnique_twistSheafBaseChangeHom`: **the comparison exists and
  is unique** with the given restriction to every chart.
* `Stacks.RelativeProj.Situation.isIso_twistSheafBaseChangeHom`: **it is an isomorphism.**

## What is and is not claimed

Tag 01O3's twist assertion is registered on
`Stacks.RelativeProj.Situation.twistSheafPullbackIso`, beside the two registrations the scheme
half already carries in
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/BaseChangeGluing.lean`.

Multiplicativity of `θ` — its compatibility with the maps `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` and with the
unit, which is what makes the family of `θ n` a homomorphism of `ℤ`-graded algebras rather than a
family of isomorphisms of modules — is **not** proved, exactly as it is not for clause (3) of Tag
01N2 in `StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeTwist.lean`. The attribute's note
says so.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.ProjTwistComparison

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue

/-! ### The chart-refinement law in the two shapes the chart descriptions consume -/

/-- **The chart-refinement law of the glueing of `𝒪(n)`, as the hypothesis of
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine`.** This is
`Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_twistMap` with its first two factors
recognised as the chart description of the inverse image along the chart comparison morphism; the
two spellings are the same term. -/
public theorem pullbackIsoOfRestrictIso_comp_twistMap (t : Situation.{u}) (n : ℤ)
    {W W' : t.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t W') (twistSheafChartIso t n W')
          (projInclusionMap t W.1 W'.1 h W.2 W'.2)
          (relativeProjChart_transition t h).symm).hom
        ≫ twistMap (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2) n
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart t W)).app
            (twistSheaf t n)).symm ≪≫ twistSheafChartIso t n W).hom :=
  ((eq_whisker (Scheme.Modules.pullbackIsoOfRestrictIso_hom (relativeProjChart t W')
        (twistSheafChartIso t n W') (projInclusionMap t W.1 W'.1 h W.2 W'.2)
        (relativeProjChart_transition t h).symm) _).trans
      (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).trans
        (eq_whisker (Scheme.Modules.pullbackCongr_symm_hom_app
          (relativeProjChart_transition t h) (twistSheaf t n)) _))).trans
    (pullbackCongr_inv_comp_twistMap t n h)

/-- The same law with the chart comparison morphism at the `AlgebraicGeometry.Proj.map` spelling,
which is the one the base-change chart members are written with. -/
public theorem pullbackIsoOfRestrictIso_comp_twistMap_projMap (t : Situation.{u}) (n : ℤ)
    {W W' : t.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t W') (twistSheafChartIso t n W')
          (AlgebraicGeometry.Proj.map (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2))
          (projMap_comp_relativeProjChart h).symm).hom
        ≫ twistMap (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2) n
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart t W)).app
            (twistSheaf t n)).symm ≪≫ twistSheafChartIso t n W).hom :=
  pullbackIsoOfRestrictIso_comp_twistMap t n h

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ))) (n : ℤ)

/-- `Stacks.RelativeProj.Situation.twistSheafPullbackChartIso` is the chart description of the
inverse image of `𝒪(n)` along the chart. True by unfolding the two definitions. -/
public theorem twistSheafPullbackChartIso_eq {T : Scheme.{u}} (W : s.base.affineOpens)
    (b : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) {hm : T ⟶ relativeProj s}
    (hfac : hm = b ≫ relativeProjChart s W) :
    twistSheafPullbackChartIso s n W b hfac
      = Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
          (twistSheafChartIso s n W) b hfac :=
  rfl

/-! ### Shrinking the affine open of `S` -/

section TargetLe

variable {W₁ W₂ : s.base.affineOpens} (h₁₂ : W₁ ≤ W₂) (W' : s'.base.affineOpens)
  (h₁ : W'.1 ≤ g ⁻¹ᵁ W₁.1) (h₂ : W'.1 ≤ g ⁻¹ᵁ W₂.1)

include h₁₂ in
/-- **The chart component of `θ n` does not change when the affine open of `S` is shrunk.** For a
fixed affine open `W'` of `S'` lying in the preimage of both `W₁ ≤ W₂`, reading `𝒪(n)` on the
chart of `S` over `W₂` and comparing with the chart twist of `s'` over `W'` is reading it on the
chart over `W₁` and comparing.

This is `Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc` for the two charts of `S`
over `W₁ ≤ W₂`: the chart-refinement law of the glueing of `𝒪(n)` is
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap`, and the factorization of
the graded base change is
`Stacks.RelativeProj.Situation.gradedBaseChange_comp_gradedRestrict`.

The chart of `Proj_{S'}(𝒜')` does not enter: both sides are morphisms out of the inverse image of
`𝒪(n)` along the one morphism `hm`. -/
public theorem twistChartBaseChangeHom_comp_eq_of_target_le
    {hm : AlgebraicGeometry.Proj (s'.sectionRingGrading W'.1) ⟶ relativeProj s}
    (hfac₁ : hm = baseChangeChart g Φ hΦ W₁ W' h₁ ≫ relativeProjChart s W₁)
    (hfac₂ : hm = baseChangeChart g Φ hΦ W₂ W' h₂ ≫ relativeProjChart s W₂) :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₂)
          (twistSheafChartIso s n W₂) (baseChangeChart g Φ hΦ W₂ W' h₂) hfac₂).hom
        ≫ twistMap (gradedBaseChange g Φ W₂.1 W'.1 h₂)
            (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ) n
      = (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₁)
            (twistSheafChartIso s n W₁) (baseChangeChart g Φ hΦ W₁ W' h₁) hfac₁).hom
        ≫ twistMap (gradedBaseChange g Φ W₁.1 W'.1 h₁)
            (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ) n :=
  twistMap_comp_pullbackChartDesc (gradedSectionRestriction s W₁.1 W₂.1 h₁₂)
    (irrelevant_le_map_gradedSectionRestriction s W₁.1 W₂.1 h₁₂ W₁.2 W₂.2)
    (gradedBaseChange g Φ W₁.1 W'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ)
    (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ) n
    (relativeProjChart s W₂) (twistSheafChartIso s n W₂)
    (relativeProjChart_transition s h₁₂).symm (twistSheafChartIso s n W₁)
    (pullbackIsoOfRestrictIso_comp_twistMap s n h₁₂) hfac₂ hfac₁
    (gradedBaseChange_comp_gradedRestrict g Φ h₁₂ W'.1 h₁ h₂).symm

include h₁₂ in
/-- **The chart component of `θ n` does not change when the affine open of `S` is shrunk**, in the
shape the glueing compatibility below consumes. This is
`Stacks.RelativeProj.Situation.twistChartBaseChangeHom_comp_eq_of_target_le`, whose two factors are
the middle two here. The outer two factors do not mention the affine open of `S`. -/
public theorem baseChangeTwistMember_target_le :
    (Scheme.Modules.pullbackComp (relativeProjChart s' W')
          (relativeProjBaseChange g Φ hΦ)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₂)
              (twistSheafChartIso s n W₂) (baseChangeChart g Φ hΦ W₂ W' h₂)
              (relativeProjChart_comp_projMap g Φ hΦ W₂ W' h₂)).hom
        ≫ twistMap (gradedBaseChange g Φ W₂.1 W'.1 h₂)
            (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W')).app (twistSheaf s' n)).symm
            ≪≫ twistSheafChartIso s' n W').inv
      = (Scheme.Modules.pullbackComp (relativeProjChart s' W')
            (relativeProjBaseChange g Φ hΦ)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₁)
              (twistSheafChartIso s n W₁) (baseChangeChart g Φ hΦ W₁ W' h₁)
              (relativeProjChart_comp_projMap g Φ hΦ W₁ W' h₁)).hom
        ≫ twistMap (gradedBaseChange g Φ W₁.1 W'.1 h₁)
            (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W')).app (twistSheaf s' n)).symm
            ≪≫ twistSheafChartIso s' n W').inv :=
  whisker_eq _
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (twistChartBaseChangeHom_comp_eq_of_target_le g Φ hΦ n h₁₂ W' h₁ h₂
            (relativeProjChart_comp_projMap g Φ hΦ W₁ W' h₁)
            (relativeProjChart_comp_projMap g Φ hΦ W₂ W' h₂)) _).trans
        (Category.assoc _ _ _)))

end TargetLe

/-! ### The chart component as a morphism of inverse images -/

/-- **The chart component of `θ n` as a morphism of inverse images** along the chart, rather than
of the restrictions. This is the `ofPullback` preimage of
`Stacks.RelativeProj.Situation.twistSheafBaseChangeRestrictHom`. -/
public def twistSheafBaseChangePullbackHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.pullback (relativeProjChart s' p.1.1)).obj
        ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n))
      ⟶ (Scheme.Modules.pullback (relativeProjChart s' p.1.1)).obj (twistSheaf s' n) :=
  ((Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
        (relativeProjBaseChange g Φ hΦ)).app (twistSheaf s n)).hom
    ≫ twistSheafBaseChangeChartHom g Φ hΦ n p
    ≫ (twistSheafChartIso s' n p.1.1).inv
    ≫ (Scheme.Modules.restrictFunctorIsoPullback
        (relativeProjChart s' p.1.1)).hom.app (twistSheaf s' n)

/-- The chart component on the restrictions is the `ofPullback` of the one on inverse images. -/
public theorem twistSheafBaseChangeRestrictHom_eq_ofPullback (p : (baseChangeCover g).I₀) :
    twistSheafBaseChangeRestrictHom g Φ hΦ n p
      = ofPullback (relativeProjChart s' p.1.1)
          (twistSheafBaseChangePullbackHom g Φ hΦ n p) := by
  simp only [ofPullback, twistSheafBaseChangePullbackHom, twistSheafBaseChangeRestrictHom,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.app_hom]

/-- **The chart component on inverse images, in the shape the generic nested lemma is stated
at.** The two differ by the bracketing of the middle factors, so one associativity step is the
whole proof.

The index of the chart cover is a *variable* here, and the pair of affine opens appears only
through its projections; against a variable the projections are inert. -/
public theorem twistSheafBaseChangePullbackHom_eq (p : (baseChangeCover g).I₀) :
    twistSheafBaseChangePullbackHom g Φ hΦ n p
      = (Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
            (relativeProjBaseChange g Φ hΦ)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s p.1.2)
              (twistSheafChartIso s n p.1.2) (baseChangeChart g Φ hΦ p.1.2 p.1.1 p.2)
              (relativeProjChart_comp_projMap g Φ hΦ p.1.2 p.1.1 p.2)).hom
        ≫ twistMap (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
            (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' p.1.1)).app (twistSheaf s' n)).symm
            ≪≫ twistSheafChartIso s' n p.1.1).inv :=
  whisker_eq _ (Category.assoc _ _ _)

/-! ### Shrinking the affine open of `S'` -/

section SourceLe

variable (W : s.base.affineOpens) {W₁' W₂' : s'.base.affineOpens} (h' : W₁' ≤ W₂')
  (h₂ : W₂'.1 ≤ g ⁻¹ᵁ W.1) (h₁ : W₁'.1 ≤ g ⁻¹ᵁ W.1)

/-- **The chart component of `θ n` over `(W, W₁')` is the inverse image of the one over
`(W, W₂')`** along the comparison morphism of the charts of `s'` attached to `W₁' ≤ W₂'`, for two
affine opens of `S'` inside the preimage of one affine open `W` of `S`.

This is `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq` for the chart of `S` over
`W` and the two charts of `S'`: the chart-refinement law of the glueing of `𝒪(n)` on `S'` is
`pullbackIsoOfRestrictIso_comp_twistMap_projMap`, and the factorization of the graded base change
is `Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange`.

Both sides are morphisms of inverse images along the chart over `W₁'`, so this is the hypothesis
`hφ` of `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`. The two chart components
are written out rather than named by
`Stacks.RelativeProj.Situation.twistSheafBaseChangePullbackHom`, whose argument is an index of the
chart cover. -/
public theorem twistSheafBaseChangePullbackHom_source_le :
    (Scheme.Modules.pullbackCongr (projMap_comp_relativeProjChart h')).inv.app
          ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n))
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))
              (relativeProjChart s' W₂')).inv.app
            ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n))
        ≫ (Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))).map
            ((Scheme.Modules.pullbackComp (relativeProjChart s' W₂')
                  (relativeProjBaseChange g Φ hΦ)).hom.app (twistSheaf s n)
              ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
                    (twistSheafChartIso s n W) (baseChangeChart g Φ hΦ W W₂' h₂)
                    (relativeProjChart_comp_projMap g Φ hΦ W W₂' h₂)).hom
              ≫ twistMap (gradedBaseChange g Φ W.1 W₂'.1 h₂)
                  (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ) n
              ≫ (((Scheme.Modules.restrictFunctorIsoPullback
                    (relativeProjChart s' W₂')).app (twistSheaf s' n)).symm
                  ≪≫ twistSheafChartIso s' n W₂').inv)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))
              (relativeProjChart s' W₂')).hom.app (twistSheaf s' n)
        ≫ (Scheme.Modules.pullbackCongr
              (projMap_comp_relativeProjChart h')).hom.app (twistSheaf s' n)
      = (Scheme.Modules.pullbackComp (relativeProjChart s' W₁')
            (relativeProjBaseChange g Φ hΦ)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
              (twistSheafChartIso s n W) (baseChangeChart g Φ hΦ W W₁' h₁)
              (relativeProjChart_comp_projMap g Φ hΦ W W₁' h₁)).hom
        ≫ twistMap (gradedBaseChange g Φ W.1 W₁'.1 h₁)
            (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W₁')).app (twistSheaf s' n)).symm
            ≪≫ twistSheafChartIso s' n W₁').inv :=
  twistMap_chartMember_pullback_eq
    (gradedBaseChange g Φ W.1 W₂'.1 h₂) (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
    (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
    (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2)
    (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ) n
    (relativeProjBaseChange g Φ hΦ) (relativeProjChart s W) (twistSheafChartIso s n W)
    (relativeProjChart s' W₂') (twistSheafChartIso s' n W₂')
    (projMap_comp_relativeProjChart h') (twistSheafChartIso s' n W₁')
    (relativeProjChart_comp_projMap g Φ hΦ W W₂' h₂)
    (relativeProjChart_comp_projMap g Φ hΦ W W₁' h₁)
    (pullbackIsoOfRestrictIso_comp_twistMap_projMap s' n h')
    (gradedRestrict_comp_gradedBaseChange g Φ W.1 h' h₂ h₁).symm

end SourceLe

/-! ### The nested case, and the glueing -/

/-- **The glueing compatibility of the chart components of `θ n` over a nested pair of indices.**
For `q ≤ p` in the index of the chart cover — that is, the affine open of `S'` and the affine open
of `S` both shrink — the two chart components act in the same way on the sections over an open of
`Proj_{S'}(𝒜')` seen by both charts.

The nested pair factors through the index with the affine open of `S'` of `q` and the affine open
of `S` of `p`: `twistSheafBaseChangePullbackHom_source_le` shrinks the open of `S'` and
`baseChangeTwistMember_target_le` then shrinks the open of `S`. -/
public theorem localApp_twistSheafBaseChangeRestrictHom_eq_of_nested
    {p q : (baseChangeCover g).I₀} (hpq : q ≤ p)
    {V : (relativeProj s').Opens}
    {U₁ : (AlgebraicGeometry.Proj (s'.sectionRingGrading p.1.1.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s'.sectionRingGrading q.1.1.1)).Opens}
    (e₁ : relativeProjChart s' p.1.1 ''ᵁ U₁ = V)
    (e₂ : relativeProjChart s' q.1.1 ''ᵁ U₂ = V) :
    localApp (relativeProjChart s' p.1.1)
        (twistSheafBaseChangeRestrictHom g Φ hΦ n p) e₁
      = localApp (relativeProjChart s' q.1.1)
        (twistSheafBaseChangeRestrictHom g Φ hΦ n q) e₂ := by
  have hle : q.1.1.1 ≤ g ⁻¹ᵁ p.1.2.1 := le_trans hpq.1 p.2
  have : IsOpenImmersion (AlgebraicGeometry.Proj.map
      (gradedSectionRestriction s' q.1.1.1 p.1.1.1 hpq.1)
      (irrelevant_le_map_gradedSectionRestriction s' q.1.1.1 p.1.1.1 hpq.1 q.1.1.2 p.1.1.2)) :=
    projInclusionMap_eq_projMap (t := s') hpq.1 ▸
      isOpenImmersion_projInclusionMap s' hpq.1 q.1.1.2 p.1.1.2
  rw [twistSheafBaseChangeRestrictHom_eq_ofPullback,
    twistSheafBaseChangeRestrictHom_eq_ofPullback,
    twistSheafBaseChangePullbackHom_eq, twistSheafBaseChangePullbackHom_eq,
    ← baseChangeTwistMember_target_le g Φ hΦ n hpq.2 q.1.1 q.2 hle]
  exact localApp_ofPullback_eq _ _ (projMap_comp_relativeProjChart hpq.1) _ _
    (twistSheafBaseChangePullbackHom_source_le g Φ hΦ n p.1.2 hpq.1 p.2 hle) e₁ e₂

/-- **The degree-`n` part of Tag 01O3's `θ` exists and is unique** with the given restriction to
every chart of the base-change cover.

This is `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the chart
cover `Stacks.RelativeProj.Situation.baseChangeCover`: the charts cover by
`iSup_image_top_baseChangeCover`, and the compatibility of two components over an arbitrary pair
of indices is `localApp_baseChangeCover_eq_of_nested` applied to the nested case. -/
public theorem existsUnique_twistSheafBaseChangeHom :
    ∃! α : (Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n) ⟶
        twistSheaf s' n,
      ∀ p : (baseChangeCover g).I₀,
        (Scheme.Modules.restrictFunctor (relativeProjChart s' p.1.1)).map α
          = twistSheafBaseChangeRestrictHom g Φ hΦ n p :=
  existsUnique_hom_of_restrict_cover
    (fun p : (baseChangeCover g).I₀ => relativeProjChart s' p.1.1)
    (iSup_image_top_baseChangeCover g) (twistSheafBaseChangeRestrictHom g Φ hΦ n)
    (fun p q U₁ U₂ V e₁ e₂ =>
      localApp_baseChangeCover_eq_of_nested g (twistSheafBaseChangeRestrictHom g Φ hΦ n)
        (fun _ _ hab _ _ _ f₁ f₂ =>
          localApp_twistSheafBaseChangeRestrictHom_eq_of_nested g Φ hΦ n hab f₁ f₂)
        p q U₁ U₂ V e₁ e₂)

/-- **The degree-`n` comparison of Tag 01O3's `θ`**, `r^* 𝒪_{Proj_S(𝒜)}(n) ⟶
𝒪_{Proj_{S'}(𝒜')}(n)`, glued from the chart components. Its defining property is
`Stacks.RelativeProj.Situation.restrictFunctor_map_twistSheafBaseChangeHom`. -/
public def twistSheafBaseChangeHom :
    (Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n) ⟶
      twistSheaf s' n :=
  (existsUnique_twistSheafBaseChangeHom g Φ hΦ n).exists.choose

/-- The comparison restricts on the chart over an index of the base-change cover to the chart
component built there. -/
public theorem restrictFunctor_map_twistSheafBaseChangeHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.restrictFunctor (relativeProjChart s' p.1.1)).map
        (twistSheafBaseChangeHom g Φ hΦ n)
      = twistSheafBaseChangeRestrictHom g Φ hΦ n p :=
  (existsUnique_twistSheafBaseChangeHom g Φ hΦ n).exists.choose_spec p

/-! ### The comparison is an isomorphism -/

/-- **The degree-`n` comparison `θ n` is an isomorphism.** Invertibility is local on
`Proj_{S'}(𝒜')`, which is covered by the charts of the base-change cover, and on each chart the
comparison is the chart component, an isomorphism by
`Stacks.RelativeProj.Situation.isIso_twistSheafBaseChangeRestrictHom`. -/
public instance isIso_twistSheafBaseChangeHom :
    IsIso (twistSheafBaseChangeHom g Φ hΦ n) := by
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _
    (fun p : (baseChangeCover g).I₀ => relativeProjChart s' p.1.1)
    (fun x => ⟨(baseChangeCover g).idx x, (baseChangeCover g).covers x⟩) fun p => ?_
  rw [restrictFunctor_map_twistSheafBaseChangeHom]
  infer_instance

/-- **The twist assertion of [Stacks, Tag 01O3].** For a morphism `g : S' ⟶ S`, relative `Proj`
situations `s` over `S` and `s'` over `S'`, and an identification `Φ` of the graded algebra of
`s'` with the pullback along `g` of that of `s`, degreewise invertible, the base-change morphism
`r : Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` carries the `n`-th twisting sheaf to the `n`-th twisting sheaf:

`θ n : r^* 𝒪_{Proj_S(𝒜)}(n) ≅ 𝒪_{Proj_{S'}(g^*𝒜)}(n)`,

for every `n : ℤ` and with no hypothesis beyond the two situations and the datum `Φ`.

The scheme half of the tag — the isomorphism `r` itself, and the cartesian square — is
`Stacks.RelativeProj.Situation.relativeProjBaseChangeIso` and
`isPullback_relativeProjBaseChange`.

Multiplicativity of `θ` is not proved: this is the degreewise isomorphism, exactly as clause (3)
of Tag 01N2 is carried by `Stacks.ProjBaseChange.isIso_twistMap_includeRight` with the same
restriction. -/
@[stacks 01O3 "the graded isomorphism θ on the twisting sheaves, in each degree separately, \
as clause (3) of Tag 01N2 is carried with the same reading",
  ega "II 2.8.10" "partial",
  ega "II 2.8.11" "more general",
  ega "II 4.1.3" "more general"]
public def twistSheafPullbackIso :
    (Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n)
      ≅ twistSheaf s' n :=
  asIso (twistSheafBaseChangeHom g Φ hΦ n)

/-- **The twist assertion of [Stacks, Tag 01O3], read on the fibre product.** The tag states `θ`
across `r^* pr₂^*`, with `pr₂ : S' ×_S Proj_S(𝒜) ⟶ Proj_S(𝒜)`; this is that reading, obtained
from `Stacks.RelativeProj.Situation.twistSheafPullbackIso` by transporting along the comparison
isomorphism with the fibre product. -/
public def twistSheafFibreProductIso :
    (Scheme.Modules.pullback (relativeProjBaseChangeIso g Φ hΦ).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (relativeProjToBase s) g)).obj (twistSheaf s n))
      ≅ twistSheaf s' n :=
  ((Scheme.Modules.pullbackComp (relativeProjBaseChangeIso g Φ hΦ).hom
        (pullback.fst (relativeProjToBase s) g)).app (twistSheaf s n))
    ≪≫ (Scheme.Modules.pullbackCongr
        (relativeProjBaseChangeIso_hom_fst g Φ hΦ)).app (twistSheaf s n)
    ≪≫ twistSheafPullbackIso g Φ hΦ n

end Stacks.RelativeProj.Situation

end
