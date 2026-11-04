module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison

/-!
# The chart-restriction comparison of a module, on sections

For a morphism `g : V ⟶ U` of étale charts of an algebraic space and an `𝒪_F`-module `M`, this
file computes on sections the two comparisons of the Zariski chart restrictions of `M`: the
direct-image comparison `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison`, a
morphism `M|_U ⟶ (chartSchemeMap g)_* M|_V`, and its transpose
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, a morphism
`(chartSchemeMap g)^* M|_U ⟶ M|_V`. On the image of the sheafification unit, each comparison is
the restriction map of `M` along a morphism of étale charts.

## Main results

* `AlgebraicGeometry.Space.toSheafify_comp_restrictToChartSchemePushforwardComparison`: the
  direct-image comparison composed with the Zariski sheafification unit of its source is the
  presheaf-level comparison `AlgebraicGeometry.Space.chartRestrictionPresheafComparison` followed
  by the sheafification unit of its target.
* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_app_toSheafify`: over a
  Zariski open `O` of the larger chart scheme, the direct-image comparison carries the
  sheafification unit of a section of `M` over `openChart U O` to the sheafification unit of its
  restriction along `AlgebraicGeometry.Space.openChartRestrict`.
* `AlgebraicGeometry.Space.unit_comp_pushforward_map_restrictToChartSchemePullbackComparison`:
  the unit of `f^* ⊣ f_*` followed by the direct image of the inverse-image comparison is the
  direct-image comparison.
* `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection`: the
  inverse-image comparison of a pulled-back section is the restriction, to the smaller open, of
  the direct-image comparison of that section.
* `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify`:
  the inverse-image comparison carries the section pulled back from the sheafification unit of a
  section `m` of `M` to the sheafification unit of the restriction of `m` along
  `openChartHomOfLE V hle ≫ openChartRestrict g O`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The direct-image comparison on sections -/

/-- **The mate computation for the direct-image comparison of the two chart restrictions.**
Composing `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison` with the Zariski
sheafification unit of its source gives the presheaf-level comparison
`AlgebraicGeometry.Space.chartRestrictionPresheafComparison` followed by the sheafification unit
of its target. -/
theorem toSheafify_comp_restrictToChartSchemePushforwardComparison
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F U)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf ≫
        (PresheafOfModules.toPresheaf (chartScheme U).ringCatSheaf.obj).map
          (restrictToChartSchemePushforwardComparison B S hS F hF M g).val =
      (PresheafOfModules.toPresheaf (chartScheme U).ringCatSheaf.obj).map
        (chartRestrictionPresheafComparison B S hS F g
            (SheafOfModules.uliftForPresentation M).val ≫
          (PresheafOfModules.pushforward (chartSchemeMap g).toRingCatSheafHom.hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (chartScheme V).ringCatSheaf.obj)).unit.app _)) :=
  (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 (chartScheme U).ringCatSheaf.obj)
      (restrictToChartSchemePushforwardComparison B S hS F hF M g)).symm.trans
    (congrArg (PresheafOfModules.toPresheaf (chartScheme U).ringCatSheaf.obj).map
      (Equiv.apply_symm_apply (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (chartScheme U).ringCatSheaf.obj)) _))

/-- **The direct-image comparison of the two chart restrictions, on a section.**  Over a Zariski
open `O` of the larger chart scheme the comparison carries the Zariski sheafification unit of a
section `m` of `M` over the étale chart `openChart U O` to the sheafification unit, over the
preimage of `O`, of the restriction of `m` along the morphism of étale charts
`AlgebraicGeometry.Space.openChartRestrict`. -/
theorem restrictToChartSchemePushforwardComparison_app_toSheafify
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (O : (chartScheme U).Opens)
    (m : ((PresheafOfModules.pushforward
      (chartSchemeRestrictionRingHom B S hS F U)).obj
        (SheafOfModules.uliftForPresentation M).val).obj (op O)) :
    (restrictToChartSchemePushforwardComparison B S hS F hF M g).val.app (op O)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F U)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) m) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme V))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F V)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf).app
          (op (chartSchemeMap g ⁻¹ᵁ O))
        ((SheafOfModules.uliftForPresentation M).val.map
          (openChartRestrict B S hS F g O).op m) :=
  ConcreteCategory.congr_hom
    (congrArg (fun t => NatTrans.app t (op O))
      (toSheafify_comp_restrictToChartSchemePushforwardComparison B S hS F hF M g)) m

/-! ### The inverse-image comparison on sections -/

/-- **The inverse-image comparison of the two chart restrictions is the transpose of the
direct-image one**, written as the triangle of the adjunction it is the transpose along: the unit
of `f^* ⊣ f_*` followed by the direct image of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison`. -/
theorem unit_comp_pushforward_map_restrictToChartSchemePullbackComparison
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    (Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).unit.app
          (restrictToChartScheme B S hS F hF M U) ≫
        (Scheme.Modules.pushforward (chartSchemeMap g)).map
          (restrictToChartSchemePullbackComparison B S hS F hF M g) =
      restrictToChartSchemePushforwardComparison B S hS F hF M g :=
  (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction
      (chartSchemeMap g)) _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The inverse-image comparison of the two chart restrictions, on a pulled-back section.**
Let `O` be a Zariski open of the larger chart scheme and `O'` one of the smaller inside its
preimage.  The comparison carries the section of `(chartSchemeMap g)^* M|_U` over `O'` pulled
back from a section `a` of `M|_U` over `O` to the restriction to `O'` of the direct-image
comparison of `a`. -/
theorem restrictToChartSchemePullbackComparison_app_pullbackSection
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens)
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (a : (restrictToChartScheme B S hS F hF M U).val.obj (op O)) :
    (restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O')
        (Scheme.Modules.pullbackSection (chartSchemeMap g)
          (restrictToChartScheme B S hS F hF M U) O O' hle a) =
      (restrictToChartScheme B S hS F hF M V).val.map (homOfLE hle).op
        ((restrictToChartSchemePushforwardComparison B S hS F hF M g).val.app (op O) a) := by
  refine (PresheafOfModules.naturality_apply
      (restrictToChartSchemePullbackComparison B S hS F hF M g).val (homOfLE hle).op
      (((Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).unit.app
        (restrictToChartScheme B S hS F hF M U)).val.app (op O) a)).trans ?_
  exact congrArg ((restrictToChartScheme B S hS F hF M V).val.map (homOfLE hle).op)
    (congrArg (fun k : restrictToChartScheme B S hS F hF M U ⟶
        (Scheme.Modules.pushforward (chartSchemeMap g)).obj
          (restrictToChartScheme B S hS F hF M V) => k.val.app (op O) a)
      (unit_comp_pushforward_map_restrictToChartSchemePullbackComparison B S hS F hF M g))

/-- **The inverse-image comparison of the two chart restrictions is the restriction map of `M`
along a morphism of étale charts.**  Let `O` be a Zariski open of the larger chart scheme, `O'`
one of the smaller inside its preimage, and `m` a section of `M` over the étale chart
`openChart U O`.  The comparison carries the section of `(chartSchemeMap g)^* M|_U` over `O'`
pulled back from the Zariski sheafification unit of `m` to the sheafification unit of the
restriction of `m` along the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O`. -/
theorem restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens)
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (m : ((PresheafOfModules.pushforward
      (chartSchemeRestrictionRingHom B S hS F U)).obj
        (SheafOfModules.uliftForPresentation M).val).obj (op O)) :
    (restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O')
        (Scheme.Modules.pullbackSection (chartSchemeMap g)
          (restrictToChartScheme B S hS F hF M U) O O' hle
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
            ((PresheafOfModules.pushforward
              (chartSchemeRestrictionRingHom B S hS F U)).obj
                (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) m)) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme V))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F V)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O')
        ((SheafOfModules.uliftForPresentation M).val.map
          (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O).op m) := by
  refine (restrictToChartSchemePullbackComparison_app_pullbackSection
    B S hS F hF M g O O' hle _).trans ?_
  refine (congrArg ((restrictToChartScheme B S hS F hF M V).val.map (homOfLE hle).op)
    (restrictToChartSchemePushforwardComparison_app_toSheafify B S hS F hF M g O m)).trans ?_
  refine (ConcreteCategory.congr_hom
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme V))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F V)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf).naturality
      (homOfLE hle).op) _).symm.trans ?_
  exact congrArg ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme V))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F V)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O'))
    (ConcreteCategory.congr_hom
      ((SheafOfModules.uliftForPresentation M).val.presheaf.map_comp
        (openChartRestrict B S hS F g O).op (openChartHomOfLE B S hS F V hle).op).symm m)

end AlgebraicGeometry.Space

end
