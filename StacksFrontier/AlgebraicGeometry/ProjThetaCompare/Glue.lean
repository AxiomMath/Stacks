module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.ChartRefine
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistChartComparison

/-!
# The twisting sheaf of a chart-indexed glueing transported to a relative `Proj`

`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjTwistChartComparison.lean`
transports the twisting sheaf of one relative `Proj` *situation* to another along a morphism given
chartwise. Its target side is a `Stacks.RelativeProj.Situation` only through four things: the
chart over each affine open of the base, the chart identification of the twist there, the graded
rings of sections with their restriction maps, and the chart-refinement law of the glueing.

**This file is that transport with the target side left as those four data.** The source side is
still a situation, because the glueing of the comparison over the chart cover — the
compatibility of two chart components over an arbitrary pair of affine opens of the base, and the
cover itself — lives there.

Instantiating the target side at the relative twists of [Stacks, Tag 01NR] is then one
application: the chart-refinement law is
`Stacks.AlgebraicGeometry.ProjThetaCompare.pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist`,
and that is the only input the two glueings of the twisting sheaves did not share.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonHom`: the chart component.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonGluedHom`: the glued comparison
  `c^* 𝒩 ⟶ 𝒪_{Proj(s)}(n)`.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonIso`: **the transport**, in every
  degree in which each chart comparison is invertible.

## Main results

* `Stacks.AlgebraicGeometry.ProjThetaCompare.localApp_chartComparisonHom_eq_of_nested`: the
  glueing compatibility over a nested pair of affine opens of the base.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.existsUnique_chartComparisonGluedHom`: the comparison
  exists and is unique with the given restriction to every chart.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.isIso_chartComparisonGluedHom`: it is an isomorphism.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjTwistComparison
open Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ProjThetaCompare

open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.RelativeProj

variable {s : Situation.{u}} {Y : Scheme.{u}} (c : relativeProj s ⟶ Y)
  {Rt : s.base.affineOpens → Type u} [∀ W, CommRing (Rt W)]
  (Bt : ∀ W : s.base.affineOpens, ℕ → AddSubgroup (Rt W)) [∀ W, GradedRing (Bt W)]
  (Nt : Y.Modules)
  (dt : ∀ W : s.base.affineOpens, AlgebraicGeometry.Proj (Bt W) ⟶ Y)
  [∀ W, IsOpenImmersion (dt W)] (n : ℤ)
  (et : ∀ W : s.base.affineOpens, Nt.restrict (dt W) ≅ twistingSheaf (Bt W) n)
  (rt : ∀ {W W' : s.base.affineOpens}, W' ≤ W → (Bt W →+*ᵍ Bt W'))
  (hrt : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W), (Bt W')₊ ≤ (Bt W)₊.map (rt h))
  (htr : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    AlgebraicGeometry.Proj.map (rt h) (hrt h) ≫ dt W = dt W')
  (hreft : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    (Scheme.Modules.pullbackIsoOfRestrictIso (dt W) (et W)
          (AlgebraicGeometry.Proj.map (rt h) (hrt h)) (htr h).symm).hom
        ≫ twistMap (rt h) (hrt h) n
      = (((Scheme.Modules.restrictFunctorIsoPullback (dt W')).app Nt).symm ≪≫ et W').hom)
  (ι : ∀ W : s.base.affineOpens, Bt W →+*ᵍ s.sectionRingGrading W.1)
  (hι : ∀ W : s.base.affineOpens, (s.sectionRingGrading W.1)₊ ≤ (Bt W)₊.map (ι W))
  (hfac : ∀ W : s.base.affineOpens, relativeProjChart s W ≫ c
    = AlgebraicGeometry.Proj.map (ι W) (hι W) ≫ dt W)

/-! ### The chart component -/

/-- **The chart component of the transport of `𝒩` over an affine open `W` of the base of `s`**, as
a morphism of inverse images along the chart: the chart description of the inverse image of `𝒩`
along the chart followed by `c`, then the twist comparison of `ι W`, then the chart description of
`𝒪_{Proj(s)}(n)` read backwards. -/
public def chartComparisonHom (W : s.base.affineOpens) :
    (Scheme.Modules.pullback (relativeProjChart s W)).obj
        ((Scheme.Modules.pullback c).obj Nt)
      ⟶ (Scheme.Modules.pullback (relativeProjChart s W)).obj (twistSheaf s n) :=
  (Scheme.Modules.pullbackComp (relativeProjChart s W) c).hom.app Nt
    ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (dt W) (et W)
        (AlgebraicGeometry.Proj.map (ι W) (hι W)) (hfac W)).hom
    ≫ twistMap (ι W) (hι W) n
    ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W)).app
        (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W).inv

/-- The chart component is an isomorphism as soon as the twist comparison of `ι W` is. -/
public theorem isIso_chartComparisonHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n))
    (W : s.base.affineOpens) :
    IsIso (chartComparisonHom c Bt Nt dt n et ι hι hfac W) := by
  have := hinv W
  unfold chartComparisonHom
  infer_instance

/-- The chart component on the restrictions is an isomorphism as well. -/
public theorem isIso_ofPullback_chartComparisonHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n))
    (W : s.base.affineOpens) :
    IsIso (ofPullback (relativeProjChart s W)
      (chartComparisonHom c Bt Nt dt n et ι hι hfac W)) := by
  have := isIso_chartComparisonHom c Bt Nt dt n et ι hι hfac hinv W
  unfold ofPullback
  infer_instance

/-! ### The mixed homomorphism of a nested pair -/

include hι in
/-- The irrelevant ideal over the smaller affine open of the base of `s` is covered by the image
of the mixed homomorphism of a nested pair: the comparison over the larger open followed by the
restriction to the smaller one. -/
public theorem irrelevant_le_sectionRestriction_comp {W W' : s.base.affineOpens} (h : W' ≤ W) :
    (s.sectionRingGrading W'.1)₊ ≤ (Bt W)₊.map
      ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (hι W)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)

omit [∀ W, IsOpenImmersion (dt W)] in
include hfac in
/-- The chart of `s` over the smaller affine open, followed by `c`, factors through the chart of
the target side over the larger one, by the mixed homomorphism. -/
public theorem relativeProjChart_comp_eq_projMap_comp {W W' : s.base.affineOpens} (h : W' ≤ W) :
    relativeProjChart s W' ≫ c
      = AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
          (irrelevant_le_sectionRestriction_comp Bt ι hι h)
        ≫ dt W := by
  rw [← projMap_comp_relativeProjChart (t := s) h, Category.assoc, hfac W, ← Category.assoc,
    Stacks.ProjModuleComparison.projMapComp (ι W) (hι W) (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2) _
      (irrelevant_le_sectionRestriction_comp Bt ι hι h) rfl]

/-! ### The nested case -/

section Nested

variable (hnest : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    (gradedSectionRestriction s W'.1 W.1 h).comp (ι W) = (ι W').comp (rt h))
  {W W' : s.base.affineOpens} (h : W' ≤ W)

include hnest hreft in
/-- **The two chart descriptions of the inverse image of `𝒩`, composed with the two twist
comparisons, agree.** This is
`Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc` for the two charts of the target
side, whose chart-refinement law is the hypothesis `hreft`. -/
public theorem chartComparisonComp_eq_of_target_le :
    (Scheme.Modules.pullbackIsoOfRestrictIso (dt W) (et W)
          (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_sectionRestriction_comp Bt ι hι h))
          (relativeProjChart_comp_eq_projMap_comp c Bt dt ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_sectionRestriction_comp Bt ι hι h) n
      = (Scheme.Modules.pullbackIsoOfRestrictIso (dt W') (et W')
            (AlgebraicGeometry.Proj.map (ι W') (hι W')) (hfac W')).hom
        ≫ twistMap (ι W') (hι W') n :=
  twistMap_comp_pullbackChartDesc (rt h) (hrt h) (ι W') (hι W')
    (irrelevant_le_sectionRestriction_comp Bt ι hι h) n
    (dt W) (et W) (htr h).symm (et W') (hreft h)
    (relativeProjChart_comp_eq_projMap_comp c Bt dt ι hι hfac h)
    (hfac W') (hnest h)

include hnest hreft in
/-- **The chart component does not change when the chart of the target side is shrunk.** -/
public theorem chartComparisonHom_eq_of_target_le :
    (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app Nt
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (dt W) (et W)
            (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
              (irrelevant_le_sectionRestriction_comp Bt ι hι h))
            (relativeProjChart_comp_eq_projMap_comp c Bt dt ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_sectionRestriction_comp Bt ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv
      = chartComparisonHom c Bt Nt dt n et ι hι hfac W' :=
  whisker_eq _ ((Category.assoc _ _ _).symm.trans
    ((eq_whisker (chartComparisonComp_eq_of_target_le c Bt Nt dt n et rt hrt htr hreft
      ι hι hfac hnest h) _).trans (Category.assoc _ _ _)))

/-- **The chart component over `W'` is the inverse image of the one over `W`** along the
comparison morphism of the charts of `s` attached to `W' ≤ W`, once the chart of the target side
is left at `W`. -/
public theorem chartComparisonHom_source_le :
    (Scheme.Modules.pullbackCongr (projMap_comp_relativeProjChart (t := s) h)).inv.app
          ((Scheme.Modules.pullback c).obj Nt)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).inv.app
            ((Scheme.Modules.pullback c).obj Nt)
        ≫ (Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))).map
            (chartComparisonHom c Bt Nt dt n et ι hι hfac W)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackCongr
            (projMap_comp_relativeProjChart (t := s) h)).hom.app (twistSheaf s n)
      = (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app Nt
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (dt W) (et W)
            (AlgebraicGeometry.Proj.map ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
              (irrelevant_le_sectionRestriction_comp Bt ι hι h))
            (relativeProjChart_comp_eq_projMap_comp c Bt dt ι hι hfac h)).hom
        ≫ twistMap ((gradedSectionRestriction s W'.1 W.1 h).comp (ι W))
            (irrelevant_le_sectionRestriction_comp Bt ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv :=
  twistMap_chartMember_pullback_eq (ι W) (hι W) (gradedSectionRestriction s W'.1 W.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)
    (irrelevant_le_sectionRestriction_comp Bt ι hι h) n c (dt W) (et W)
    (relativeProjChart s W) (twistSheafChartIso s n W)
    (projMap_comp_relativeProjChart (t := s) h) (twistSheafChartIso s n W') (hfac W)
    (relativeProjChart_comp_eq_projMap_comp c Bt dt ι hι hfac h)
    (pullbackIsoOfRestrictIso_comp_twistMap_projMap s n h) rfl

include hnest hreft h in
/-- **The glueing compatibility of the chart components over a nested pair of affine opens of the
base of `s`.** -/
public theorem localApp_chartComparisonHom_eq_of_nested {V : (relativeProj s).Opens}
    {U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens}
    (e₁ : relativeProjChart s W ''ᵁ U₁ = V) (e₂ : relativeProjChart s W' ''ᵁ U₂ = V) :
    localApp (relativeProjChart s W)
        (ofPullback (relativeProjChart s W)
          (chartComparisonHom c Bt Nt dt n et ι hι hfac W)) e₁
      = localApp (relativeProjChart s W')
        (ofPullback (relativeProjChart s W')
          (chartComparisonHom c Bt Nt dt n et ι hι hfac W')) e₂ := by
  have : IsOpenImmersion (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)) :=
    projInclusionMap_eq_projMap (t := s) h ▸ isOpenImmersion_projInclusionMap s h W'.2 W.2
  exact localApp_ofPullback_eq _ _ (projMap_comp_relativeProjChart (t := s) h) _ _
    ((chartComparisonHom_source_le c Bt Nt dt n et ι hι hfac h).trans
      (chartComparisonHom_eq_of_target_le c Bt Nt dt n et rt hrt htr hreft ι hι hfac hnest h))
    e₁ e₂

end Nested

/-! ### The glued comparison -/

variable (hnest : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
  (gradedSectionRestriction s W'.1 W.1 h).comp (ι W) = (ι W').comp (rt h))

include hnest hreft in
/-- **The transport of `𝒩` along `c` exists and is unique** with the given restriction to every
chart of `Proj(s)`. -/
public theorem existsUnique_chartComparisonGluedHom :
    ∃! α : (Scheme.Modules.pullback c).obj Nt ⟶ twistSheaf s n,
      ∀ W : s.base.affineOpens,
        (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map α
          = ofPullback (relativeProjChart s W)
            (chartComparisonHom c Bt Nt dt n et ι hι hfac W) :=
  existsUnique_hom_of_restrict_cover (relativeProjChart s)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange]
      using iSup_opensRange_relativeProjChart s)
    (fun W => ofPullback (relativeProjChart s W)
      (chartComparisonHom c Bt Nt dt n et ι hι hfac W))
    (fun W W' U₁ U₂ V e₁ e₂ =>
      localApp_relativeProjChart_eq_of_nested
        (fun W => ofPullback (relativeProjChart s W)
          (chartComparisonHom c Bt Nt dt n et ι hι hfac W))
        (fun _ _ hle _ _ _ f₁ f₂ =>
          localApp_chartComparisonHom_eq_of_nested c Bt Nt dt n et rt hrt htr hreft
            ι hι hfac hnest hle f₁ f₂)
        W W' U₁ U₂ V e₁ e₂)

include Bt dt et rt hrt htr hreft ι hι hfac hnest in
/-- **The transport of `𝒩` along `c`**, glued from the chart components. -/
public def chartComparisonGluedHom :
    (Scheme.Modules.pullback c).obj Nt ⟶ twistSheaf s n :=
  (existsUnique_chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft
    ι hι hfac hnest).exists.choose

include hnest hreft in
/-- The transport restricts on the chart over an affine open of the base of `s` to the chart
component built there. -/
public theorem restrictFunctor_map_chartComparisonGluedHom (W : s.base.affineOpens) :
    (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map
        (chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft ι hι hfac hnest)
      = ofPullback (relativeProjChart s W)
        (chartComparisonHom c Bt Nt dt n et ι hι hfac W) :=
  (existsUnique_chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft
    ι hι hfac hnest).exists.choose_spec W

include hnest hreft in
/-- **The transport is an isomorphism** as soon as the twist comparison of each `ι W` is. -/
public theorem isIso_chartComparisonGluedHom
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n)) :
    IsIso (chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft ι hι hfac hnest) := by
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ (relativeProjChart s)
    (fun x => exists_relativeProjChart_eq s x) fun W => ?_
  rw [restrictFunctor_map_chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft
    ι hι hfac hnest W]
  exact isIso_ofPullback_chartComparisonHom c Bt Nt dt n et ι hι hfac hinv W

include Bt dt et rt hrt htr hreft ι hι hfac hnest in
/-- **The twisting sheaf of the target side transported along a chartwise comparison**:
`c^* 𝒩 ≅ 𝒪_{Proj(s)}(n)`, in every degree in which each chart comparison is invertible. -/
public def chartComparisonIso
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n)) :
    (Scheme.Modules.pullback c).obj Nt ≅ twistSheaf s n :=
  have := isIso_chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft ι hι hfac hnest hinv
  asIso (chartComparisonGluedHom c Bt Nt dt n et rt hrt htr hreft ι hι hfac hnest)

end Stacks.AlgebraicGeometry.ProjThetaCompare

end
