module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueing

/-!
# The Zariski chart restriction of a quasi-coherent module

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `M` be a
quasi-coherent `𝒪_X`-module.  Restricting `M` to an étale scheme chart `A` gives a sheaf of
modules `M|_A` on the *Zariski* site of `chartScheme A`
(`AlgebraicGeometry.Space.restrictToChartScheme`), and this file proves the two properties of
that restriction which the scheme-level results of Stacks 060M and Stacks 05JZ consume:

* it is quasi-coherent on the Zariski site of the chart scheme, and
* along a morphism of charts it is the pullback of the restriction to the larger chart.

Both were carried as hypotheses by the consumers of the chart restriction; here they are proved
from quasi-coherence of `M` alone.

## Main definitions

* `AlgebraicGeometry.Space.openChartFunctorIso` identifies the index functor of the chart
  restriction, `AlgebraicGeometry.Space.openChartFunctor`, with the composite comparison functor
  `AlgebraicGeometry.Space.chartComparisonFunctor` of the two localizations.
* `AlgebraicGeometry.Space.restrictToChartSchemeIsoRestrictModule` presents the chart restriction
  as the restriction, along the inclusion of the small Zariski site of the chart scheme, of the
  reading of `M` on the small étale site of that scheme.

## Main results

* `AlgebraicGeometry.Space.isContinuous_openChartFunctor`: the index functor of the chart
  restriction is continuous, at every étale chart of every algebraic space.
* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`: **the chart restriction of a
  quasi-coherent module is quasi-coherent on the Zariski site of the chart scheme.**
* `AlgebraicGeometry.Space.nonempty_pullback_restrictToChartScheme`: **along a morphism of étale
  charts the chart restriction is the pullback of the restriction to the larger chart.**

## Implementation notes

**Continuity of the index functor.**  `AlgebraicGeometry.Space.openChartFunctor` and
`AlgebraicGeometry.Space.chartComparisonFunctor` send a Zariski open of the chart scheme to the
same étale chart of `X` — that is
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj` — but not by `rfl`: the two
differ in how the open immersion is taken into the size-bounded category of schemes.  The
isomorphism of functors is therefore assembled from `CategoryTheory.eqToIso`, and its naturality
is proved with `AlgebraicGeometry.Space.hom_ext_of_toScheme_map_eq`, a morphism of étale charts
being determined by its underlying morphism of schemes: after that passage both squares are
`Scheme.homOfLE` against an identity.  Continuity transports along the isomorphism, and that is
what makes `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` — the presentation of
the chart restriction as a single direct image — available at an arbitrary chart rather than
only at the identity chart of a represented algebraic space.

**The comparison of structure maps** is the one of
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, at the chart's own object of the
big fppf category: over a Zariski open, three of the four factors of
`AlgebraicGeometry.Space.chartComparisonRingMap` are identities — the counit of the
identification of the two small étale sites at a chart cut out by a Zariski open is the identity
because morphisms into such a chart are unique, the two steps of the localization of Stacks 04M0
carry the identity as their structure map, and the component of the identification of the index
functors is a map of global regular functions on one and the same scheme — and the surviving
factor is `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` on the nose.

**Quasi-coherence** is then Descent, Proposition 03DX: the chart restriction is the restriction
along the inclusion of the small Zariski site of the chart scheme of
`AlgebraicGeometry.Space.chartSchemeEtaleModule`, which is quasi-coherent on the small étale site
of that scheme, and
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` carries quasi-coherence across that
inclusion with no hypothesis.  This is the step which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionQuasicoherent.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean` record as unavailable; it is
available.

**The base change along a morphism of charts** is
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, the
represented case, applied at the morphism of the big fppf category underlying the morphism of
charts, together with the identification of the restriction of `M` to the smaller chart with the
inverse image of its restriction to the larger one.  The latter is
`AlgebraicGeometry.Space.chartModuleRestrictionComp`, Stacks 03LY, read through
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks 03LW: the restriction of
`M` to the small étale site of a chart is its étale restriction along the structure morphism of
the chart, on the nose.  The result is an isomorphism rather than invertibility of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`; the canonical comparison is
not identified with it here, and the consumers transport local projectivity, which only needs an
isomorphism.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The index functor of the chart restriction -/

/-- The morphism of schemes underlying an equality of étale charts is the corresponding equality
of chart schemes. -/
theorem toScheme_map_toOver_map_eqToHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P Q : SmallEtale B S hS F} (h : P = Q) (hs : chartScheme P = chartScheme Q) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (eqToHom h))
      = eqToHom hs := by
  subst h; simp

/-- **The index functor of the chart restriction is the composite comparison functor.**  Both
send a Zariski open of the chart scheme to the étale chart of `X` that it cuts out; the two
readings of that chart agree by
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`.

Naturality is checked after the passage to schemes, where both squares read
`Scheme.homOfLE` against an identity: a morphism of étale charts is determined by its underlying
morphism of schemes. -/
def openChartFunctorIso (A : SmallEtale B S hS X.1) :
    openChartFunctor B S hS X.1 A ≅ chartComparisonFunctor B S hS X A :=
  NatIso.ofComponents
    (fun V => eqToIso (openChart_eq_chartLocalization_opensObj B S hS X A V).symm)
    (fun {V' V} i => by
      apply hom_ext_of_toScheme_map_eq
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
      change (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (openChartHomOfLE B S hS X.1 A i.le)) ≫
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (eqToHom (openChart_eq_chartLocalization_opensObj B S hS X A V).symm)) =
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (eqToHom (openChart_eq_chartLocalization_opensObj B S hS X A V').symm)) ≫
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
            (openChartOfComparisonHom B S hS X A i.le))
      rw [toScheme_map_toOver_map_eqToHom B S hS
          (openChart_eq_chartLocalization_opensObj B S hS X A V).symm rfl,
        toScheme_map_toOver_map_eqToHom B S hS
          (openChart_eq_chartLocalization_opensObj B S hS X A V').symm rfl,
        toScheme_map_toOver_map_openChartOfComparisonHom]
      change (chartScheme A).homOfLE i.le ≫ 𝟙 _ = 𝟙 _ ≫ (chartScheme A).homOfLE i.le
      simp)

/-- **The index functor of the chart restriction is continuous**, from the small Zariski site of
the chart scheme to the small étale site of `X`: it is isomorphic to the composite comparison
functor, which is. -/
theorem isContinuous_openChartFunctor (A : SmallEtale B S hS X.1) :
    (openChartFunctor B S hS X.1 A).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS X.1) :=
  Functor.isContinuous_of_iso (openChartFunctorIso B S hS X A).symm _ _

/-! ### The chart restriction as a direct image -/

/-- **The chart restriction of `M` is the direct image of `M` along the composite comparison
functor.**  The chart restriction is a direct image along
`AlgebraicGeometry.Space.openChartFunctor`, which is continuous and isomorphic to
`AlgebraicGeometry.Space.chartComparisonFunctor`; the two structure maps agree because all but
one of the factors of `AlgebraicGeometry.Space.chartComparisonRingMap` are identities over a
Zariski open. -/
def restrictToChartSchemeIsoChartComparison (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (A : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS X.1 X.2 M A ≅
      (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M := by
  haveI := isContinuous_openChartFunctor B S hS X A
  refine restrictToChartSchemeIsoPushforward B S hS X.2 A M ≪≫
    ((SheafOfModules.pushforwardCongr₂ (chartComparisonRingMap B S hS X A)
      (ψ := chartSchemeRestrictionSheafHom B S hS X.2 A)
      (openChartFunctorIso B S hS X A) ?_).app M).symm
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun O => ?_)
  have hX1 : (((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) (chartScheme A)
          (chartFppfObject B S hS X A).left.property).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥(chartScheme A))
          (AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property)).map
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
          (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).hom.app O
      = 𝟙 _ := by
    have h1 : (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).counit.app
        (SmallEtale.opensObj (associatedBigEtaleSite B) (chartScheme A)
          (chartFppfObject B S hS X A).left.property O.unop) = 𝟙 _ :=
      @Subsingleton.elim _ (SmallEtale.subsingleton_hom_opensToSmallEtale
        (associatedBigEtaleSite B) (chartScheme A)
        (chartFppfObject B S hS X A).left.property _ O.unop) _ _
    change (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map
        ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).counit.app
          (SmallEtale.opensObj (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property O.unop)).op = 𝟙 _
    exact (congrArg (fun k => (representedSchemeStructureSheaf B S hS
          (chartFppfObject B S hS X A)).obj.map (Quiver.Hom.op k)) h1).trans
      ((congrArg (representedSchemeStructureSheaf B S hS
          (chartFppfObject B S hS X A)).obj.map op_id).trans
        ((representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)).obj.map_id _))
  have hX2 : (((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property ⋙
          (representedSmallEtaleEquivalence B S hS
            (chartFppfObject B S hS X A)).inverse).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥(chartScheme A))
          (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))).map
        (chartComparisonRingMapEtale B S hS X A)).hom.app O = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  have hX3 : ((Functor.sheafPushforwardContinuousNatTrans (openChartFunctorIso B S hS X A).hom
          RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme A))
          (SmallEtale.topology B S hS X.1)).app (structureRingSheaf B S hS X)).hom.app O
      = 𝟙 _ := by
    change (structureRingSheaf B S hS X).obj.map
      (eqToHom (openChart_eq_chartLocalization_opensObj B S hS X A O.unop).symm).op = 𝟙 _
    exact (congrArg (structureRingSheaf B S hS X).obj.map (eqToHom_op _)).trans
      ((eqToHom_map (structureRingSheaf B S hS X).obj _).trans rfl)
  change ((_ ≫ _) ≫ _) ≫ _ = _
  rw [hX1, hX2, hX3]
  exact ((Category.comp_id _).trans (Category.comp_id _)).trans (Category.comp_id _)

/-- **The chart restriction of a quasi-coherent module is the restriction, along the inclusion of
the small Zariski site of the chart scheme, of its reading on the small étale site of that
scheme.** -/
def restrictToChartSchemeIsoRestrictModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS X.1 X.2 M A ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A) :=
  restrictToChartSchemeIsoChartComparison B S hS X M A ≪≫
    eqToIso (restrictModule_chartSchemeEtaleModule_eq_pushforward B S hS X M hM A).symm

/-! ### Quasi-coherence of the chart restriction -/

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module is quasi-coherent** on the Zariski
site of the chart scheme.

The chart restriction is the restriction along the inclusion of the small Zariski site of the
chart scheme of a module which is quasi-coherent on the small étale site of that scheme, and that
restriction preserves quasi-coherence by Descent, Proposition 03DX. -/
theorem isQuasicoherent_restrictToChartScheme
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (restrictToChartScheme B S hS X.1 X.2 M A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).prop_of_iso
    (restrictToChartSchemeIsoRestrictModule B S hS X M hM A).symm
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
      (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS X A).left.property (chartSchemeEtaleModule B S hS X M hM A)
      (chartSchemeEtaleQcoh B S hS X M hM A).property)

/-! ### Base change of the chart restriction along a morphism of charts -/

/-- The restriction of `M` to the small étale site of a chart is the inverse image of `M` of
Stacks 03LU along the structure morphism of the chart: along an étale morphism that inverse image
is étale restriction, Stacks 03LW, and étale restriction along the structure morphism of a chart
*is* the restriction to the chart. -/
def chartModuleRestrictionIsoChartSmallEtaleRestriction
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1) :
    (chartModuleRestriction B S hS X A).obj M ≅ chartSmallEtaleRestriction B S hS X M A :=
  (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
    (isEtale_chartToSpace B S hS X A)).app M

/-- **The restriction of `M` to a smaller chart is the inverse image of its restriction to the
larger one**, on the small étale sites of the two chart spaces.  This is Stacks 03LY, read
through the identification of the restriction to a chart with the inverse image along the
structure morphism of the chart. -/
def chartSmallEtaleRestrictionPullbackIso
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {A' A : SmallEtale B S hS X.1} (g : A' ⟶ A) :
    (modulePullback B S hS (chartMap B S hS X g)).obj (chartSmallEtaleRestriction B S hS X M A) ≅
      chartSmallEtaleRestriction B S hS X M A' :=
  (chartModuleInverseImage B S hS X g).mapIso
      (chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X M A).symm ≪≫
    (chartModuleRestrictionComp B S hS X g).app M ≪≫
    chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X M A'

/-- The chart restriction of `M` at an étale chart `A` is the chart restriction, at the identity
chart of the algebraic space represented by the chart's own object of the big fppf category, of
the reading of `M` on the small étale site of that represented space. -/
def restrictToChartSchemeIsoIdEtaleChart
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS X.1 X.2 M A ≅
      restrictToChartScheme B S hS (yoneda.obj (chartFppfObject B S hS X A))
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X A))
        (chartSmallEtaleRestriction B S hS X M A)
        (idEtaleChart B S hS (chartFppfObject B S hS X A)) :=
  restrictToChartSchemeIsoRestrictModule B S hS X M hM A ≪≫
    (restrictToChartSchemeIdEtaleChartIso B S hS (chartFppfObject B S hS X A)
      (chartSmallEtaleRestriction B S hS X M A)).symm

/-- **Along a morphism `g : A' ⟶ A` of étale charts the chart restriction of a quasi-coherent
module is the pullback of the restriction to the larger chart**, along the morphism of chart
schemes.

Both chart restrictions are chart restrictions at the identity chart of a represented algebraic
space, where the base-change statement is
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`; the
inverse image of the restriction of `M` to `A` is its restriction to `A'` by Stacks 03LY. -/
theorem nonempty_pullback_restrictToChartScheme
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    {A' A : SmallEtale B S hS X.1} (g : A' ⟶ A) :
    Nonempty ((Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS X.1 X.2 M A) ≅
      restrictToChartScheme B S hS X.1 X.2 M A') := by
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent
    ((SmallEtale.toOver B S hS X.1).map g) (chartSmallEtaleRestriction B S hS X M A)
    (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS X M hM A)
  refine ⟨(Scheme.Modules.pullback (chartSchemeMap g)).mapIso
      (restrictToChartSchemeIsoIdEtaleChart B S hS X M hM A) ≪≫ e.symm ≪≫ ?_ ≪≫
    (restrictToChartSchemeIsoIdEtaleChart B S hS X M hM A').symm⟩
  exact (restrictToChartSchemeFunctor B S hS
      (yoneda.obj (chartFppfObject B S hS X A'))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X A'))
      (idEtaleChart B S hS (chartFppfObject B S hS X A'))).mapIso
    (chartSmallEtaleRestrictionPullbackIso B S hS X M g)

end AlgebraicGeometry.Space

end
