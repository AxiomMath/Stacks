module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The chart restriction of a quasi-coherent module is the chart-scheme transport

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, let `M` be a
quasi-coherent `𝒪_X`-module and let `A` be an étale scheme chart of `X`.  Two constructions
carry `M` to a module on the Zariski site of the chart's scheme:
`AlgebraicGeometry.Space.restrictToChart` restricts the sections along
`AlgebraicGeometry.Space.openChartFunctor` and sheafifies, while
`AlgebraicGeometry.Space.chartSchemeModule` goes through the comparison equivalences of
Stacks 04M0 and of Descent, Proposition 03DX (2).  This file identifies the two.

## Main definitions

* `AlgebraicGeometry.Space.openChartFunctorIsoChartComparisonFunctor`: the identification of the
  index functor of the chart restriction with the composite comparison functor of the chart.
* `AlgebraicGeometry.Space.restrictToChartSchemeIsoChartComparisonPushforward`,
  `AlgebraicGeometry.Space.restrictToChartSchemeIsoChartSchemeModule` and
  `AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule`: the two readings of the chart
  restriction are isomorphic to the chart-scheme transport.

## Main results

* `Stacks.SheafOfModules.pushforwardIsoOfIndexEq`: two direct images along *equal* index functors
  with the same structure map are isomorphic.
* `AlgebraicGeometry.Space.openChartFunctor_eq_chartComparisonFunctor`: the two index functors
  are equal.
* `AlgebraicGeometry.Space.chartComparisonRingMap_comp_sheafPushforwardContinuousNatTrans`: the
  two structure maps are compatible with that identification.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_restrictToChart_eq`: the chart restriction and
  the chart-scheme transport have the same weakly associated points.

## Implementation notes

The equality of the two index functors is used through `CategoryTheory.NatIso.ofComponents`
rather than through `CategoryTheory.eqToIso`, because `SheafOfModules.pushforwardCongr₂` asks for
the component of the comparison at each Zariski open, and the component of
`CategoryTheory.eqToIso` at an equality of functors is not that component on the nose.

Each step is stated as its own declaration: assembled into a single proof they exhaust the
heartbeat budget.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}

/-- **Transport of a direct image of sheaves of modules across an equality of index functors.**
If the two index functors are equal and the two structure maps are heterogeneously equal, then
the two direct images are isomorphic. -/
noncomputable def pushforwardIsoOfIndexEq {K L : C ⥤ D} (e : K = L)
    [K.IsContinuous J T] [L.IsContinuous J T]
    {Sh : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf T RingCat.{w}}
    {φ : Sh ⟶ (L.sheafPushforwardContinuous RingCat.{w} J T).obj R}
    {ψ : Sh ⟶ (K.sheafPushforwardContinuous RingCat.{w} J T).obj R}
    (h : HEq φ ψ) :
    _root_.SheafOfModules.pushforward.{w} φ ≅ _root_.SheafOfModules.pushforward.{w} ψ := by
  subst e
  obtain rfl := eq_of_heq h
  exact Iso.refl _

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The two index functors -/

/-- The index functor of the chart restriction and the composite comparison functor of the chart
agree on each Zariski open of the chart's scheme. -/
theorem openChartFunctor_obj_eq_chartComparisonFunctor_obj (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    (openChartFunctor B S hS X.1 A).obj V = (chartComparisonFunctor B S hS X A).obj V :=
  (openChart_eq_chartLocalization_opensObj B S hS X A V).symm

/-- **The index functor of the chart restriction is the composite comparison functor of the
chart.** -/
theorem openChartFunctor_eq_chartComparisonFunctor (A : SmallEtale B S hS X.1) :
    openChartFunctor B S hS X.1 A = chartComparisonFunctor B S hS X A :=
  CategoryTheory.Functor.ext
    (openChartFunctor_obj_eq_chartComparisonFunctor_obj B S hS X A)
    (fun _ _ _ => by
      apply hom_ext_of_toScheme_map_eq
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        eqToHom_map, eqToHom_map, eqToHom_map, eqToHom_map]
      rfl)

/-- The identification of the two index functors, as an isomorphism of functors. -/
noncomputable def openChartFunctorIsoChartComparisonFunctor (A : SmallEtale B S hS X.1) :
    openChartFunctor B S hS X.1 A ≅ chartComparisonFunctor B S hS X A :=
  NatIso.ofComponents
    (fun V => eqToIso (openChartFunctor_obj_eq_chartComparisonFunctor_obj B S hS X A V))
    (fun _ => by
      apply hom_ext_of_toScheme_map_eq
      rw [eqToIso.hom, eqToIso.hom, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, eqToHom_map, eqToHom_map, eqToHom_map, eqToHom_map]
      rfl)

/-- **The index functor of the chart restriction is continuous** from the small Zariski site of
the chart's scheme to the small étale site of `X`. -/
instance isContinuous_openChartFunctor (A : SmallEtale B S hS X.1) :
    (openChartFunctor B S hS X.1 A).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS X.1) :=
  Functor.isContinuous_of_iso
    (openChartFunctorIsoChartComparisonFunctor B S hS X A).symm _ _

/-! ### The two structure maps -/

/-- The counit of the comparison of the two small étale sites is the identity at the étale chart
which a Zariski open of the chart's scheme cuts out. -/
theorem counit_representedSmallEtaleEquivalence_opensObj (A : SmallEtale B S hS X.1)
    (O : (chartScheme A).Opens) :
    (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property O) = 𝟙 _ :=
  @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
    (associatedBigEtaleSite B) (chartScheme A)
    (chartFppfObject B S hS X A).left.property _ O) _ _

/-- The structure map of the comparison of the two small étale sites is the identity at the
étale chart which a Zariski open of the chart's scheme cuts out. -/
theorem reindexBackSharp_hom_app_opensObj (A : SmallEtale B S hS X.1)
    (O : (chartScheme A).Opens) :
    (Stacks.SheafOfModules.reindexBackSharp
        (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
        (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
        (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).hom.app
      (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property O)) = 𝟙 _ := by
  show (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property O)).op = 𝟙 _
  exact (congrArg (fun k =>
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map
        (Quiver.Hom.op k)) (counit_representedSmallEtaleEquivalence_opensObj B S hS X A O)).trans
    ((congrArg (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map
      op_id).trans
      ((representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map_id _))

/-- The map of structure sheaves induced by the comparison of the two index functors is the
identity at each Zariski open of the chart's scheme. -/
theorem sheafPushforwardContinuousNatTrans_openChartFunctorIso_app
    (A : SmallEtale B S hS X.1) (O : (Opens ↥(chartScheme A))ᵒᵖ) :
    ((Functor.sheafPushforwardContinuousNatTrans
        (openChartFunctorIsoChartComparisonFunctor B S hS X A).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme A))
        (SmallEtale.topology B S hS X.1)).app
      (structureRingSheaf B S hS X)).hom.app O = 𝟙 _ := by
  show (structureRingSheaf B S hS X).obj.map
    (eqToHom (openChartFunctor_obj_eq_chartComparisonFunctor_obj B S hS X A O.unop)).op = 𝟙 _
  exact (congrArg (structureRingSheaf B S hS X).obj.map (eqToHom_op _)).trans
    ((eqToHom_map (structureRingSheaf B S hS X).obj _).trans rfl)

/-- **The composite structure map of a chart and the structure map of the chart restriction are
compatible with the comparison of the two index functors.** -/
theorem chartComparisonRingMap_comp_sheafPushforwardContinuousNatTrans
    (A : SmallEtale B S hS X.1) :
    chartComparisonRingMap B S hS X A ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (openChartFunctorIsoChartComparisonFunctor B S hS X A).hom
          RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme A))
          (SmallEtale.topology B S hS X.1)).app (structureRingSheaf B S hS X) =
      chartSchemeRestrictionSheafHom B S hS X.2 A := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun O => ?_)
  show (chartComparisonRingMap B S hS X A).hom.app O ≫
      ((Functor.sheafPushforwardContinuousNatTrans
        (openChartFunctorIsoChartComparisonFunctor B S hS X A).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme A))
        (SmallEtale.topology B S hS X.1)).app
      (structureRingSheaf B S hS X)).hom.app O =
    (chartSchemeRestrictionSheafHom B S hS X.2 A).hom.app O
  refine (congrArg (fun k => (chartComparisonRingMap B S hS X A).hom.app O ≫ k)
      (sheafPushforwardContinuousNatTrans_openChartFunctorIso_app B S hS X A O)).trans ?_
  refine (Category.comp_id ((chartComparisonRingMap B S hS X A).hom.app O)).trans ?_
  refine RingCat.hom_ext ?_
  rw [chartComparisonRingMap_hom_app]
  show RingHom.comp _ _ = _
  rw [reindexBackSharp_hom_app_opensObj]
  rfl

/-! ### The chart restriction is the chart-scheme transport -/

/-- **The restriction of an `𝒪_X`-module to the scheme of an étale chart is the direct image of
the module along the composite comparison functor of the chart.** -/
noncomputable def restrictToChartSchemeIsoChartComparisonPushforward
    (A : SmallEtale B S hS X.1) (N : Modules.{u, u} B S hS X.1 X.2) :
    restrictToChartScheme B S hS X.1 X.2 N A ≅
      (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj N :=
  restrictToChartSchemeIsoPushforward B S hS X.2 A N ≪≫
    ((SheafOfModules.pushforwardCongr₂ (chartComparisonRingMap B S hS X A)
      (ψ := chartSchemeRestrictionSheafHom B S hS X.2 A)
      (openChartFunctorIsoChartComparisonFunctor B S hS X A)
      (chartComparisonRingMap_comp_sheafPushforwardContinuousNatTrans B S hS X A)).app N).symm

/-- **The Zariski reading of the chart restriction of a quasi-coherent `𝒪_X`-module is the
chart-scheme transport.** -/
noncomputable def restrictToChartSchemeIsoChartSchemeModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS X.1 X.2 M A ≅ chartSchemeModule B S hS X M hM A :=
  restrictToChartSchemeIsoChartComparisonPushforward B S hS X A M ≪≫
    eqToIso (restrictModule_chartSchemeEtaleModule_eq_pushforward B S hS X M hM A).symm ≪≫
      (chartSchemeModuleIsoRestrictModule B S hS X M hM A).symm

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module is the chart-scheme transport.** -/
noncomputable def restrictToChartIsoChartSchemeModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    restrictToChart B S hS X.2 M A ≅ chartSchemeModule B S hS X M hM A :=
  restrictToChartIsoRestrictToChartScheme B S hS X.2 M A ≪≫
    restrictToChartSchemeIsoChartSchemeModule B S hS X M hM A

/-- **The chart restriction and the chart-scheme transport have the same weakly associated
points**, in the Zariski sense of Stacks 056L. -/
theorem weaklyAssociatedPoints_restrictToChart_eq
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    Stacks.Divisors.weaklyAssociatedPoints (restrictToChart B S hS X.2 M A) =
      Stacks.Divisors.weaklyAssociatedPoints (chartSchemeModule B S hS X M hM A) :=
  Set.ext fun x =>
    Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso
      (restrictToChartIsoChartSchemeModule B S hS X M hM A) x

end AlgebraicGeometry.Space

end
