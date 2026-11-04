module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingGermsOnOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary

/-!
# The commuting square of local rings of Stacks 05VU

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `x̄` be a geometric
point of `X` and let `U ⟶ V` be a commuting square of étale scheme charts over `f` together
with a lift of `x̄` to `U`.  Writing `u` for the point of `U` under that lift and `v` for its
image in `V`, there are two composites of ring homomorphisms

`𝒪_{V, v} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}`  and  `𝒪_{V, v} → 𝒪_{U, u} → 𝒪_{X, x̄}`,

the first through the canonical map of Stacks 05VP and the homomorphism of étale local rings of
Stacks 04NG, the second through the stalk map of the vertical morphism of schemes and again
Stacks 05VP.  This file proves that they agree; the square of local rings drawn in the proof of
Stacks 05VU commutes.

## Main definitions

* `AlgebraicGeometry.Space.chartOpenOverRestrict` is the restriction of the vertical morphism of
  the square to a Zariski open of the target chart and its preimage, as a morphism of the site.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing`: **the
  commuting square of local rings of Stacks 05VU**, as an identity of ring homomorphisms.
* `AlgebraicGeometry.Space.etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ_open`: the same
  identity read on the germ at `v` of a regular function on a Zariski open of the target chart.
* `AlgebraicGeometry.Space.etaleLocalRingMap_etaleLocalRingGerm_eq`: the same identity read on
  a global regular function of the target chart, with the left-hand side written as
  `AlgebraicGeometry.Space.etaleLocalRingGerm`.
* `AlgebraicGeometry.Space.chartOpens_obj_hom_comp` and
  `AlgebraicGeometry.Space.chartOpenNeighborhood_point_comp_restrict`: the refined square of
  pointed étale charts given by a Zariski open of the target chart and its preimage commutes
  over `f` and respects the chosen lifts.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The refined square of étale charts -/

/-- The restriction of the vertical morphism of a commuting square of étale scheme charts to a
Zariski open of the target chart and its preimage, as a morphism of the site. -/
noncomputable def chartOpenOverRestrict (N : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : N.obj.left ⟶ V.obj.left) (W : (chartScheme V).Opens) :
    chartOpenOver B S hS N (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) ⟶
      chartOpenOver B S hS V W :=
  Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).map g) ∣_ W)) (by
    apply B.inclusion.map_injective
    change (((BigFppfOver.toScheme B S hS).map g) ∣_ W) ≫ (W.ι ≫ V.obj.left.hom.1) =
      (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W).ι ≫ N.obj.left.hom.1
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    congr 1
    exact congrArg B.inclusion.map g.w)

/-- The restricted morphism is compatible with the inclusions of the two opens. -/
theorem chartOpenOverRestrict_comp_ι (N : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : N.obj.left ⟶ V.obj.left) (W : (chartScheme V).Opens) :
    chartOpenOverRestrict B S hS N V g W ≫ chartOpenOverι B S hS V W =
      chartOpenOverι B S hS N (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) ≫ g := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  exact morphismRestrict_ι ((BigFppfOver.toScheme B S hS).map g) W

/-- The scheme morphism underlying the restricted morphism of the refined square is the
restriction of the scheme morphism of the original square. -/
theorem toScheme_map_chartOpenOverRestrict (N : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : N.obj.left ⟶ V.obj.left) (W : (chartScheme V).Opens) :
    (BigFppfOver.toScheme B S hS).map (chartOpenOverRestrict B S hS N V g W) =
      ((BigFppfOver.toScheme B S hS).map g) ∣_ W := rfl

variable {f : X ⟶ Y} {xbar : GeometricPoint B S hS X}

/-- The refined square of étale scheme charts given by a Zariski open of the target chart and
its preimage commutes over `f`. -/
theorem chartOpens_obj_hom_comp (N : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : N.obj.left ⟶ V.obj.left) (W : (chartScheme V).Opens)
    (hcomm : N.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom) :
    ((chartOpens B S hS N).obj (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W)).obj.hom ≫ f =
      yoneda.map (chartOpenOverRestrict B S hS N V g W) ≫
        ((chartOpens B S hS V).obj W).obj.hom := by
  show (yoneda.map (chartOpenOverι B S hS N _) ≫ N.obj.hom) ≫ f =
    yoneda.map (chartOpenOverRestrict B S hS N V g W) ≫
      yoneda.map (chartOpenOverι B S hS V W) ≫ V.obj.hom
  rw [Category.assoc, hcomm, ← Category.assoc, ← yoneda.map_comp,
    ← chartOpenOverRestrict_comp_ι, yoneda.map_comp, Category.assoc]

/-- The chosen lifts of the geometric points into the two opens of the refined square are
carried to one another by the restricted morphism. -/
theorem chartOpenNeighborhood_point_comp_restrict
    (N : SmallEtaleNeighborhood xbar) (Wc : SmallEtale B S hS Y)
    (g : N.chart.obj.left ⟶ Wc.obj.left)
    (hcomm : N.chart.obj.hom ≫ f = yoneda.map g ≫ Wc.obj.hom)
    (W : (chartScheme Wc).Opens)
    (hu : chartPoint B S hS X N ∈ ((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W)
    (hv : chartPoint B S hS Y (targetNeighborhood B S hS N Wc g hcomm) ∈ W) :
    (chartOpenNeighborhood B S hS N (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) hu).point ≫
        chartOpenOverRestrict B S hS N.chart Wc g W =
      (chartOpenNeighborhood B S hS (targetNeighborhood B S hS N Wc g hcomm) W hv).point := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show chartOpenLift B S hS N (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) hu ≫
      (((BigFppfOver.toScheme B S hS).map g) ∣_ W) =
    chartOpenLift B S hS (targetNeighborhood B S hS N Wc g hcomm) W hv
  refine (cancel_mono W.ι).1 ?_
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, chartOpenLift_comp]
  refine Eq.trans ?_
    (chartOpenLift_comp B S hS (targetNeighborhood B S hS N Wc g hcomm) W hv).symm
  exact ((BigFppfOver.toScheme B S hS).map_comp N.point g).symm

/-! ### The commuting square of local rings -/

section Square

variable {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
  (xbar : GeometricPoint B S hS Xs.1) (N : SmallEtaleNeighborhood xbar)
  (Wc : SmallEtale B S hS Ys.1) (g : N.chart.obj.left ⟶ Wc.obj.left)
  (hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map g ≫ Wc.obj.hom)
  (W : (chartScheme Wc).Opens)

/-- **The commuting square of local rings of Stacks 05VU on a germ.**  The germ at `v` of a
regular function on a Zariski open of the chart of `Y` is sent, going round the square either
way, to the germ at `x̄` of its pullback. -/
theorem etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ_open
    (hu : chartPoint B S hS Xs.1 N ∈ ((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W)
    (hv : chartPoint B S hS Ys.1 (targetNeighborhood B S hS N Wc g hcomm) ∈ W)
    (a : Γ(chartScheme Wc, W)) :
    etaleLocalRingMap Xs.2 f.hom xbar
        (chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2
          (targetNeighborhood B S hS N Wc g hcomm)
          ((chartScheme Wc).presheaf.germ W
            (chartPoint B S hS Ys.1 (targetNeighborhood B S hS N Wc g hcomm)) hv a)) =
      chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
        ((((BigFppfOver.toScheme B S hS).map g).stalkMap
            (chartPoint B S hS Xs.1 N)).hom
          ((chartScheme Wc).presheaf.germ W
            (chartPoint B S hS Ys.1 (targetNeighborhood B S hS N Wc g hcomm)) hv a)) := by
  have hsq := etaleLocalRingMap_isEtaleLocalRingMap Xs.2 f.hom xbar
    (chartOpenNeighborhood B S hS N (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) hu)
    (chartOpenNeighborhood B S hS (targetNeighborhood B S hS N Wc g hcomm) W hv)
    (chartOpenOverRestrict B S hS N.chart Wc g W)
    (chartOpens_obj_hom_comp B S hS N.chart Wc g W hcomm)
    (chartOpenNeighborhood_point_comp_restrict B S hS N Wc g hcomm W hu hv)
  refine Eq.trans (congrArg (etaleLocalRingMap Xs.2 f.hom xbar)
    (chartLocalRingToEtaleLocalRing_germ_open B S hS Ys.2
      (targetNeighborhood B S hS N Wc g hcomm) W hv a)) ?_
  refine Eq.trans (congrArg (fun k => k (W.topIso.inv a)) hsq).symm ?_
  refine Eq.trans (congrArg
    (etaleLocalRingGerm B S hS Xs.1 xbar
      (op (chartOpenNeighborhood B S hS N
        (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) hu)))
    (ConcreteCategory.congr_hom
      (topIso_inv_comp_Γ_map_morphismRestrict ((BigFppfOver.toScheme B S hS).map g) W) a)) ?_
  refine Eq.trans (chartLocalRingToEtaleLocalRing_germ_open B S hS Xs.2 N
    (((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ W) hu
    ((((BigFppfOver.toScheme B S hS).map g).app W).hom a)).symm ?_
  exact congrArg (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N)
    (Scheme.Hom.germ_stalkMap_apply ((BigFppfOver.toScheme B S hS).map g) W
      (chartPoint B S hS Xs.1 N) hu a).symm

/-- **The commuting square of local rings of Stacks 05VU.**  In a commuting square of étale
scheme charts over `f : X ⟶ Y` carrying a lift of a geometric point `x̄`, the two composites
`𝒪_{V, v} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}` and `𝒪_{V, v} → 𝒪_{U, u} → 𝒪_{X, x̄}` agree. -/
theorem etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing :
    (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).comp
        ((((BigFppfOver.toScheme B S hS).map g).stalkMap
          (chartPoint B S hS Xs.1 N)).hom) =
      (etaleLocalRingMap Xs.2 f.hom xbar).comp
        (chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2
          (targetNeighborhood B S hS N Wc g hcomm)) := by
  refine RingHom.ext fun c => ?_
  obtain ⟨W, hw, a, ha⟩ := TopCat.Presheaf.exists_germ_eq (chartScheme Wc).presheaf c
  show chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
      ((((BigFppfOver.toScheme B S hS).map g).stalkMap
        (chartPoint B S hS Xs.1 N)).hom c) =
    etaleLocalRingMap Xs.2 f.hom xbar
      (chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2
        (targetNeighborhood B S hS N Wc g hcomm) c)
  rw [← ha]
  exact (etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ_open B S hS f xbar N Wc g
    hcomm W hw hw a).symm

/-- **The germ at `x̄` of a regular function on a chart of the target is the image of its
Zariski germ on the chart of the source.**  For a commuting square of étale charts over
`f : X ⟶ Y` carrying a lift of a geometric point `x̄`, the germ in `𝒪_{Y, ȳ}` of a global
regular function `a` on the chart `V` of `Y`, pushed into `𝒪_{X, x̄}` by the canonical
homomorphism of Stacks 04NG, is the image under the canonical map of Stacks 05VP of the Zariski
germ at `u` of the pullback of `a` to the chart `U` of `X`. -/
theorem etaleLocalRingMap_etaleLocalRingGerm_eq (a : Γ(chartScheme Wc, ⊤)) :
    etaleLocalRingMap Xs.2 f.hom xbar
        (etaleLocalRingGerm B S hS Ys.1 (geometricPointMap f.hom xbar)
          (op (targetNeighborhood B S hS N Wc g hcomm)) a) =
      chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
        ((((BigFppfOver.toScheme B S hS).map g).stalkMap
            (chartPoint B S hS Xs.1 N)).hom
          ((chartScheme Wc).presheaf.germ ⊤
            (chartPoint B S hS Ys.1 (targetNeighborhood B S hS N Wc g hcomm)) trivial a)) := by
  refine Eq.trans (congrArg (etaleLocalRingMap Xs.2 f.hom xbar)
    (chartLocalRingToEtaleLocalRing_germ B S hS Ys.1 Ys.2
      (targetNeighborhood B S hS N Wc g hcomm) a).symm) ?_
  exact (RingHom.congr_fun
    (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS f xbar N Wc g hcomm) _).symm

end Square

end AlgebraicGeometry.Space

end
