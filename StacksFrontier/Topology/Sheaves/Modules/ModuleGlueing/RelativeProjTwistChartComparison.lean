module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.ComparisonChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorGlue
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafExact
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistBaseChangeGlued

/-!
# The twisting sheaves across a chartwise comparison of two relative projective spectra

Let `s` and `t` be relative `Proj` situations and let `c : Proj(s) ⟶ Proj(t)` be a morphism which
is given chartwise: an affine open `κ W` of the base of `t` for every affine open `W` of the base
of `s`, monotone in `W`, and a homomorphism `ι W` of the graded rings of local sections over `κ W`
and over `W` for which

`chart_s W ≫ c = Proj.map (ι W) ≫ chart_t (κ W)`,

compatibly with the restriction maps.  This file carries the twisting sheaves across `c`: for
every `n : ℤ`,

`c^* 𝒪_{Proj(t)}(n) ⟶ 𝒪_{Proj(s)}(n)`,

glued from the twist comparisons `Stacks.ProjTwistComparison.twistMap` of the `ι W`, and an
isomorphism as soon as each of those is.

## The route

`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` glues the chart
components, asking that two of them agree over the overlap of their charts for an **arbitrary**
pair of affine opens of the base of `s`.  The reduction to a *nested* pair is already proved and
mentions neither sheaf: `Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested`.
The nested case splits in two, as it does for the base-change comparison of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjTwistBaseChangeGlued.lean`:

* the chart of `s` shrinks — `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq`, whose
  hypothesis is the chart-refinement law
  `Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap` of the glueing of
  `𝒪(n)` on `Proj(s)`;
* the chart of `t` then shrinks — `Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc`,
  with the same law on `Proj(t)`.

The two are composed through the compatibility of `ι` with the restriction maps, which identifies
the mixed homomorphism the first step produces with the one the second step consumes.

Invertibility is local on the charts, and a morphism of sheaves of modules whose restrictions
along a jointly surjective family of open immersions are isomorphisms is one, by
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`.

## Why the comparison is presented chartwise

The data above is what an isomorphism of relative-`Proj` gluing data
(`Stacks.RelativeProj.Data.Iso`) gives, with `κ` the identity; it is stated at bare chart data
here, for two unrelated situations, because that keeps every term in the statements below built
from variables.  Instantiating it afterwards costs one application, while carrying the
instantiated terms through the glueing does not fit in the kernel's budget.

## Main definitions

* `Stacks.RelativeProj.Situation.twistChartComparisonHom`: the chart component, as a morphism of
  inverse images along the chart.
* `Stacks.RelativeProj.Situation.twistChartComparisonGluedHom`: the glued comparison
  `c^* 𝒪_{Proj(t)}(n) ⟶ 𝒪_{Proj(s)}(n)`.
* `Stacks.RelativeProj.Situation.twistChartComparisonIso`: **the transport of the twisting sheaf
  along `c`**, in every degree.

## Main results

* `Stacks.RelativeProj.Situation.twistChartComparisonHom_source_le` and
  `twistChartComparisonHom_eq_of_target_le`: the two halves of the nested case.
* `Stacks.RelativeProj.Situation.localApp_twistChartComparisonHom_eq_of_nested`: the glueing
  compatibility over a nested pair of affine opens of the base of `s`.
* `Stacks.RelativeProj.Situation.existsUnique_twistChartComparisonGluedHom`: the comparison exists
  and is unique with the given restriction to every chart.
* `Stacks.RelativeProj.Situation.isIso_twistChartComparisonGluedHom`: it is an isomorphism.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open Stacks.ProjTwistComparison

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue

variable {s t : Situation.{u}} (c : relativeProj s ⟶ relativeProj t)
  (κ : s.base.affineOpens → t.base.affineOpens)
  (hκ : ∀ {W W' : s.base.affineOpens}, W' ≤ W → κ W' ≤ κ W)
  (ι : ∀ W : s.base.affineOpens, t.sectionRingGrading (κ W).1 →+*ᵍ s.sectionRingGrading W.1)
  (hι : ∀ W : s.base.affineOpens,
    (s.sectionRingGrading W.1)₊ ≤ (t.sectionRingGrading (κ W).1)₊.map (ι W))
  (hfac : ∀ W : s.base.affineOpens, relativeProjChart s W ≫ c
    = AlgebraicGeometry.Proj.map (ι W) (hι W) ≫ relativeProjChart t (κ W))
  (n : ℤ)

/-! ### The chart component -/

/-- **The chart component of the transport of `𝒪_{Proj(t)}(n)` over an affine open `W` of the base
of `s`**, as a morphism of inverse images along the chart: the chart description of the inverse
image of `𝒪_{Proj(t)}(n)` along the chart followed by `c`, then the twist comparison of `ι W`,
then the chart description of `𝒪_{Proj(s)}(n)` read backwards. -/
public def twistChartComparisonHom (W : s.base.affineOpens) :
    (Scheme.Modules.pullback (relativeProjChart s W)).obj
        ((Scheme.Modules.pullback c).obj (twistSheaf t n))
      ⟶ (Scheme.Modules.pullback (relativeProjChart s W)).obj (twistSheaf s n) :=
  (Scheme.Modules.pullbackComp (relativeProjChart s W) c).hom.app (twistSheaf t n)
    ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t (κ W))
        (twistSheafChartIso t n (κ W)) (AlgebraicGeometry.Proj.map (ι W) (hι W)) (hfac W)).hom
    ≫ twistMap (ι W) (hι W) n
    ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W)).app
        (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W).inv

/-- The chart component is an isomorphism as soon as the twist comparison of `ι W` is: the three
chart descriptions always are. -/
public theorem isIso_twistChartComparisonHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n))
    (W : s.base.affineOpens) : IsIso (twistChartComparisonHom c κ ι hι hfac n W) := by
  have := hinv W
  unfold twistChartComparisonHom
  infer_instance

/-- The chart component on the restrictions is an isomorphism as well. -/
public theorem isIso_ofPullback_twistChartComparisonHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n))
    (W : s.base.affineOpens) :
    IsIso (ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W)) := by
  have := isIso_twistChartComparisonHom c κ ι hι hfac n hinv W
  unfold ofPullback
  infer_instance

/-! ### The mixed homomorphism of a nested pair -/

include hι in
/-- The irrelevant ideal over the smaller affine open of the base of `s` is covered by the image
of the mixed homomorphism of a nested pair: the comparison over the larger open followed by the
restriction to the smaller one. -/
public theorem irrelevant_le_gradedSectionRestriction_comp {W W' : s.base.affineOpens}
    (h : W' ≤ W) :
    (s.sectionRingGrading W'.1)₊ ≤ (t.sectionRingGrading (κ W).1)₊.map
      ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (hι W)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)

include hfac in
/-- The chart of `s` over the smaller affine open, followed by `c`, factors through the chart of
`t` over the larger one, by the mixed homomorphism.  This is the chart transition law of `Proj(s)`
and the chartwise factorization of `c` composed through
`Stacks.ProjModuleComparison.projMapComp`. -/
public theorem relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp
    {W W' : s.base.affineOpens} (h : W' ≤ W) :
    relativeProjChart s W' ≫ c
      = AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
          (irrelevant_le_gradedSectionRestriction_comp κ ι hι h)
        ≫ relativeProjChart t (κ W) := by
  rw [← projMap_comp_relativeProjChart (t := s) h, Category.assoc, hfac W, ← Category.assoc,
    Stacks.ProjModuleComparison.projMapComp (ι W) (hι W) (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2) _
      (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) rfl]

/-! ### The nested case -/

section Nested

variable (hnest : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    (gradedSectionRestriction s W'.1 W.1 h).comp (ι W)
      = (ι W').comp (gradedSectionRestriction t (κ W').1 (κ W).1 (hκ h)))
  {W W' : s.base.affineOpens} (h : W' ≤ W)

include hnest in
/-- **The two chart descriptions of the inverse image of `𝒪_{Proj(t)}(n)`, composed with the two
twist comparisons, agree.** Reading it on the chart of `t` over `κ W` and comparing with the chart
twist of `s` over `W'` is reading it on the chart over `κ W'` and comparing.

This is `Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc` for the two charts of `t`,
whose chart-refinement law is
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap` and whose
factorization of the mixed homomorphism is the compatibility of `ι` with the restriction maps. -/
public theorem twistChartComparisonComp_eq_of_target_le :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t (κ W))
          (twistSheafChartIso t n (κ W))
          (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_gradedSectionRestriction_comp κ ι hι h))
          (relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp c κ ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) n
      = (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t (κ W'))
            (twistSheafChartIso t n (κ W')) (AlgebraicGeometry.Proj.map (ι W') (hι W'))
            (hfac W')).hom
        ≫ twistMap (ι W') (hι W') n :=
  twistMap_comp_pullbackChartDesc
    (gradedSectionRestriction t (κ W').1 (κ W).1 (hκ h))
    (irrelevant_le_map_gradedSectionRestriction t (κ W').1 (κ W).1 (hκ h) (κ W').2 (κ W).2)
    (ι W') (hι W') (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) n
    (relativeProjChart t (κ W)) (twistSheafChartIso t n (κ W))
    (projMap_comp_relativeProjChart (t := t) (hκ h)).symm (twistSheafChartIso t n (κ W'))
    (pullbackIsoOfRestrictIso_comp_twistMap_projMap t n (hκ h))
    (relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp c κ ι hι hfac h)
    (hfac W') (hnest h)

include hnest in
/-- **The chart component does not change when the chart of `t` is shrunk.** This is
`Stacks.RelativeProj.Situation.twistChartComparisonComp_eq_of_target_le`, whose two factors are
the middle two here; the outer two mention only the chart of `s` over `W'`. -/
public theorem twistChartComparisonHom_eq_of_target_le :
    (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app (twistSheaf t n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t (κ W))
            (twistSheafChartIso t n (κ W))
            (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
              (irrelevant_le_gradedSectionRestriction_comp κ ι hι h))
            (relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp
              c κ ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv
      = twistChartComparisonHom c κ ι hι hfac n W' :=
  whisker_eq _ ((Category.assoc _ _ _).symm.trans
    ((eq_whisker (twistChartComparisonComp_eq_of_target_le c κ hκ ι hι hfac n hnest h) _).trans
      (Category.assoc _ _ _)))

/-- **The chart component over `W'` is the inverse image of the one over `W`** along the
comparison morphism of the charts of `s` attached to `W' ≤ W`, once the chart of `t` is left at
`κ W`.

This is `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq` for the chart of `t` over
`κ W` and the two charts of `s`, with the chart-refinement law
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap` on `Proj(s)` as its
hypothesis.  Both sides are morphisms of inverse images along the chart over `W'`, so this is the
hypothesis `hφ` of `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`; the mixed
component on the right is written out, since it is not the component of any single chart. -/
public theorem twistChartComparisonHom_source_le :
    (Scheme.Modules.pullbackCongr (projMap_comp_relativeProjChart (t := s) h)).inv.app
          ((Scheme.Modules.pullback c).obj (twistSheaf t n))
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).inv.app
            ((Scheme.Modules.pullback c).obj (twistSheaf t n))
        ≫ (Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))).map
            (twistChartComparisonHom c κ ι hι hfac n W)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackCongr
            (projMap_comp_relativeProjChart (t := s) h)).hom.app (twistSheaf s n)
      = (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app (twistSheaf t n)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t (κ W))
            (twistSheafChartIso t n (κ W))
            (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
              (irrelevant_le_gradedSectionRestriction_comp κ ι hι h))
            (relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp c κ ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv :=
  twistMap_chartMember_pullback_eq (ι W) (hι W) (gradedSectionRestriction s W'.1 W.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)
    (irrelevant_le_gradedSectionRestriction_comp κ ι hι h) n c (relativeProjChart t (κ W))
    (twistSheafChartIso t n (κ W)) (relativeProjChart s W) (twistSheafChartIso s n W)
    (projMap_comp_relativeProjChart (t := s) h) (twistSheafChartIso s n W') (hfac W)
    (relativeProjChart_comp_eq_projMap_gradedSectionRestriction_comp c κ ι hι hfac h)
    (pullbackIsoOfRestrictIso_comp_twistMap_projMap s n h) rfl

include hnest h in
/-- **The glueing compatibility of the chart components over a nested pair of affine opens of the
base of `s`.** For `W' ≤ W` the two chart components act in the same way on the sections over an
open of `Proj(s)` seen by both charts.

`Stacks.RelativeProj.Situation.twistChartComparisonHom_source_le` shrinks the chart of `s` and
`twistChartComparisonHom_eq_of_target_le` then shrinks the chart of `t`. -/
public theorem localApp_twistChartComparisonHom_eq_of_nested {V : (relativeProj s).Opens}
    {U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens}
    (e₁ : relativeProjChart s W ''ᵁ U₁ = V) (e₂ : relativeProjChart s W' ''ᵁ U₂ = V) :
    localApp (relativeProjChart s W)
        (ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W)) e₁
      = localApp (relativeProjChart s W')
        (ofPullback (relativeProjChart s W') (twistChartComparisonHom c κ ι hι hfac n W')) e₂ := by
  have : IsOpenImmersion (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)) :=
    projInclusionMap_eq_projMap (t := s) h ▸ isOpenImmersion_projInclusionMap s h W'.2 W.2
  exact localApp_ofPullback_eq _ _ (projMap_comp_relativeProjChart (t := s) h) _ _
    ((twistChartComparisonHom_source_le c κ ι hι hfac n h).trans
      (twistChartComparisonHom_eq_of_target_le c κ hκ ι hι hfac n hnest h)) e₁ e₂

end Nested

/-! ### The glued comparison -/

variable (hnest : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
  (gradedSectionRestriction s W'.1 W.1 h).comp (ι W)
    = (ι W').comp (gradedSectionRestriction t (κ W').1 (κ W).1 (hκ h)))

include hnest in
/-- **The transport of `𝒪_{Proj(t)}(n)` along `c` exists and is unique** with the given
restriction to every chart of `Proj(s)`.

This is `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the chart
cover: the charts cover by
`Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart`, and the compatibility of two
components over an arbitrary pair of affine opens of the base is
`Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested` applied to the nested
case. -/
public theorem existsUnique_twistChartComparisonGluedHom :
    ∃! α : (Scheme.Modules.pullback c).obj (twistSheaf t n) ⟶ twistSheaf s n,
      ∀ W : s.base.affineOpens,
        (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map α
          = ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W) :=
  existsUnique_hom_of_restrict_cover (relativeProjChart s)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange]
      using iSup_opensRange_relativeProjChart s)
    (fun W => ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W))
    (fun W W' U₁ U₂ V e₁ e₂ =>
      localApp_relativeProjChart_eq_of_nested
        (fun W => ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W))
        (fun _ _ hle _ _ _ f₁ f₂ =>
          localApp_twistChartComparisonHom_eq_of_nested c κ hκ ι hι hfac n hnest hle f₁ f₂)
        W W' U₁ U₂ V e₁ e₂)

include κ hκ ι hι hfac hnest in
/-- **The transport of `𝒪_{Proj(t)}(n)` along `c`**, glued from the chart components.  Its
defining property is
`Stacks.RelativeProj.Situation.restrictFunctor_map_twistChartComparisonGluedHom`. -/
public def twistChartComparisonGluedHom :
    (Scheme.Modules.pullback c).obj (twistSheaf t n) ⟶ twistSheaf s n :=
  (existsUnique_twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest).exists.choose

include hnest in
/-- The transport restricts on the chart over an affine open of the base of `s` to the chart
component built there. -/
public theorem restrictFunctor_map_twistChartComparisonGluedHom (W : s.base.affineOpens) :
    (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map
        (twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest)
      = ofPullback (relativeProjChart s W) (twistChartComparisonHom c κ ι hι hfac n W) :=
  (existsUnique_twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest).exists.choose_spec W

include hnest in
/-- **The transport is an isomorphism** as soon as the twist comparison of each `ι W` is.
Invertibility is local on `Proj(s)`, which is covered by its charts, and on each chart the
transport is the chart component. -/
public theorem isIso_twistChartComparisonGluedHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n)) :
    IsIso (twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest) := by
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ (relativeProjChart s)
    (fun x => exists_relativeProjChart_eq s x) fun W => ?_
  rw [restrictFunctor_map_twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest W]
  exact isIso_ofPullback_twistChartComparisonHom c κ ι hι hfac n hinv W

include κ hκ ι hι hfac hnest in
/-- **The twisting sheaf of `Proj(t)` transported along a chartwise comparison**:
`c^* 𝒪_{Proj(t)}(n) ≅ 𝒪_{Proj(s)}(n)`, in every degree in which each chart comparison is
invertible. -/
public def twistChartComparisonIso
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n)) :
    (Scheme.Modules.pullback c).obj (twistSheaf t n) ≅ twistSheaf s n :=
  haveI := isIso_twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest hinv
  asIso (twistChartComparisonGluedHom c κ hκ ι hι hfac n hnest)

end Stacks.RelativeProj.Situation

end
