module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear

/-!
# The chart restriction of a module on an algebraic space is a direct image

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be a
quasi-coherent `𝒪_X`-module and let `A` be an étale scheme chart of `X`. The chart restriction of
`M` is the composite of four `CategoryTheory.SheafOfModules.pushforward`s — the slice at the
chart, the comparison of Stacks 04M0, the comparison of the representable case of Stacks 03ED,
and the inclusion of the small Zariski site. Since `CategoryTheory.SheafOfModules.pushforwardComp`
is `CategoryTheory.Iso.refl`, it is the direct image of `M` along a single continuous functor from
the small Zariski site of the chart's scheme to the small étale site of `X`, with a single
morphism of sheaves of rings as its structure map.

## Main definitions

* `AlgebraicGeometry.Space.chartComparisonFunctor`: the composite comparison functor
  `(chartScheme A).Opens ⥤ SmallEtale B S hS X.1`, which sends a Zariski open of the chart's
  scheme to the étale chart of `X` it cuts out.
* `AlgebraicGeometry.Space.chartComparisonRingMap`: the composite structure map, whose
  component over a Zariski open is `AlgebraicGeometry.Space.chartSectionsRingHom`.
* `AlgebraicGeometry.Space.openChartOfComparisonHom`: the morphism of étale charts which an
  inclusion of Zariski opens induces, the morphism-level counterpart of
  `AlgebraicGeometry.Space.openChartOfComparison`.

## Main results

* `Stacks.SheafOfModules.pushforward_obj_val_presheaf_map`: the restriction maps of a pushforward
  of sheaves of modules are the restriction maps of the target along the image of the morphism.
* `Stacks.SheafOfModules.pushforward_four_obj`: four pushforwards of sheaves of modules are the
  pushforward along the composite of the four functors, with the composite structure map.
* `AlgebraicGeometry.Space.chartComparisonFunctor_obj`,
  `AlgebraicGeometry.Space.chartComparisonFunctor_map`: the composite comparison functor is
  `AlgebraicGeometry.Space.openChartOfComparison` on objects and
  `AlgebraicGeometry.Space.openChartOfComparisonHom` on morphisms, by `rfl`.
* `AlgebraicGeometry.Space.chartComparisonRingMap_hom_app`: the component of the composite
  structure map over a Zariski open is `AlgebraicGeometry.Space.chartSectionsRingHom`, by `rfl`.
* `AlgebraicGeometry.Space.hom_ext_of_toScheme_map_eq`: a morphism of étale charts is determined
  by its underlying morphism of schemes.
* `AlgebraicGeometry.Space.chartScheme_openChartOfComparison` and
  `AlgebraicGeometry.Space.toScheme_map_toOver_map_openChartOfComparisonHom`: the composite
  comparison functor agrees with `AlgebraicGeometry.Space.openChartFunctor` after the passage to
  schemes, on objects and on morphisms, by `rfl`.
* `AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_eq_pushforward`: the chart
  restriction of `M` to the small Zariski site of the chart's scheme is the direct image of `M`
  along the composite comparison functor.
* `AlgebraicGeometry.Space.chartComparisonPushforward_obj_val_obj` and
  `AlgebraicGeometry.Space.chartComparisonPushforward_presheaf_map`: its sections and its
  restriction maps.

## Implementation notes

The collapse is a single application of the four-layer
`Stacks.SheafOfModules.pushforward_four_obj`: chaining the two-layer collapse with `congrArg`
leaves the universes of the intermediate `CategoryTheory.SheafOfModules` category undetermined.
The composite functor is grouped as `(F₁ ⋙ F₂) ⋙ (F₃ ⋙ F₄)`, and the composite structure map to
match, as that lemma produces; another grouping is definitionally equal but forces the
instantiation to re-check it.

The topologies are spelled at `yoneda.obj (chartFppfObject …)`, not at `(chartSpace …).1`:
instance search for continuity is syntactic and fails at the second spelling, so the continuity of
the comparison functor of Stacks 04M0 is re-registered here at the first.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

universe w m v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  {Q : CategoryTheory.Sheaf L RingCat.{w}}
  [F.IsContinuous J K] [G.IsContinuous K L]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{w} K L).obj Q)

/-- The restriction map of the direct image of `N` along a continuous functor `F` and a morphism
of sheaves of rings `φ`, along a morphism `f` of the source site, is the restriction map of `N`
along `F.map f`, as maps of the underlying abelian presheaves. -/
theorem pushforward_obj_val_presheaf_map (N : _root_.SheafOfModules.{m} R) {A A' : C}
    (f : A' ⟶ A) :
    ((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.presheaf.map f.op
      = N.val.presheaf.map (F.map f).op := rfl

section FourLayers

universe v₄ v₅ u₄ u₅

variable {E₄ : Type u₄} [Category.{v₄} E₄] {E₅ : Type u₅} [Category.{v₅} E₅]
  {L₄ : GrothendieckTopology E₄} {L₅ : GrothendieckTopology E₅}
  {G₃ : E ⥤ E₄} {G₄ : E₄ ⥤ E₅}
  {Q₄ : CategoryTheory.Sheaf L₄ RingCat.{w}} {Q₅ : CategoryTheory.Sheaf L₅ RingCat.{w}}
  [G₃.IsContinuous L L₄] [G₄.IsContinuous L₄ L₅]
  (χ : Q ⟶ (G₃.sheafPushforwardContinuous RingCat.{w} L L₄).obj Q₄)
  (ω : Q₄ ⟶ (G₄.sheafPushforwardContinuous RingCat.{w} L₄ L₅).obj Q₅)

/-- The iterated direct image of `N` along four continuous functors and four morphisms of sheaves
of rings is the direct image along the composite of the four functors, with the composite morphism
of sheaves of rings as its structure map. -/
theorem pushforward_four_obj (N : _root_.SheafOfModules.{m} Q₅) :
    haveI : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp _ _ _ K _
    haveI : (G₃ ⋙ G₄).IsContinuous L L₅ := Functor.isContinuous_comp _ _ _ L₄ _
    haveI : ((F ⋙ G) ⋙ (G₃ ⋙ G₄)).IsContinuous J L₅ := Functor.isContinuous_comp _ _ _ L _
    (_root_.SheafOfModules.pushforward.{m} φ).obj
        ((_root_.SheafOfModules.pushforward.{m} ψ).obj
          ((_root_.SheafOfModules.pushforward.{m} χ).obj
            ((_root_.SheafOfModules.pushforward.{m} ω).obj N)))
      = (_root_.SheafOfModules.pushforward.{m} (F := (F ⋙ G) ⋙ (G₃ ⋙ G₄))
          ((φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map ψ) ≫
            ((F ⋙ G).sheafPushforwardContinuous RingCat.{w} J L).map
              (χ ≫ (G₃.sheafPushforwardContinuous RingCat.{w} L L₄).map ω))).obj N := rfl

end FourLayers

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-! ### The composite comparison functor -/

/-- The composite comparison functor of a chart: the inclusion of the small Zariski site of the
chart's scheme into its small étale site, followed by the inverse of the comparison of that site
with the small étale site of the chart space, the comparison equivalence of Stacks 04M0, and the
projection of the slice at the chart. It sends a Zariski open of the chart's scheme to the étale
chart of `X` which that open cuts out. -/
noncomputable abbrev chartComparisonFunctor (A : SmallEtale B S hS X.1) :
    (chartScheme A).Opens ⥤ SmallEtale B S hS X.1 :=
  ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property) ⋙
    (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).inverse) ⋙
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor ⋙ Over.forget A)

/-- The composite comparison functor sends a Zariski open of the chart's scheme to the étale
chart of `X` which it cuts out. -/
theorem chartComparisonFunctor_obj (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    (chartComparisonFunctor B S hS X A).obj V = openChartOfComparison B S hS X A V := rfl

/-- The morphism of étale charts of `X` which an inclusion of Zariski opens of a chart's scheme
induces, through the comparison of the two small étale sites and the localization of Stacks 04M0
at the chart. -/
noncomputable abbrev openChartOfComparisonHom (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V) :
    openChartOfComparison B S hS X A V' ⟶ openChartOfComparison B S hS X A V :=
  (chartComparisonFunctor B S hS X A).map (homOfLE h)

/-- The composite comparison functor acts on an inclusion of Zariski opens as the induced
morphism of étale charts. -/
theorem chartComparisonFunctor_map (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V) :
    (chartComparisonFunctor B S hS X A).map (homOfLE h)
      = openChartOfComparisonHom B S hS X A h := rfl

/-- A morphism of étale charts is determined by its underlying morphism of schemes. -/
theorem hom_ext_of_toScheme_map_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P Q : SmallEtale B S hS F} {a b : P ⟶ Q}
    (hab : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a)
      = (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map b)) : a = b :=
  ObjectProperty.hom_ext _ <| CostructuredArrow.hom_ext _ _ <| Over.OverMorphism.ext <|
    B.inclusion.map_injective hab

/-- The scheme of the étale chart which the comparison equivalences attach to a Zariski open of a
chart's scheme is, definitionally, that open subscheme. -/
theorem chartScheme_openChartOfComparison (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    chartScheme (openChartOfComparison B S hS X A V) = V.toScheme := rfl

/-- The morphism of schemes underlying the morphism of étale charts induced by an inclusion of
Zariski opens is, definitionally, the inclusion of the open subschemes. -/
theorem toScheme_map_toOver_map_openChartOfComparisonHom (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
        (openChartOfComparisonHom B S hS X A h))
      = (chartScheme A).homOfLE h := rfl

/-! ### Continuity of the composite comparison functor -/

/-- The comparison functor of Stacks 04M0 at a chart is continuous, for the topology of the chart
space spelled as the small étale topology of `yoneda.obj` of the chart's object. -/
instance isContinuous_chartLocalizationEquivalence_yoneda (A : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      ((SmallEtale.topology B S hS X.1).over A) :=
  isContinuous_chartLocalization_chartSpace B S hS X A

/-- The comparison equivalence of Stacks 04M0 followed by the projection of the slice at the
chart is continuous. -/
instance isContinuous_chartLocalizationEquivalence_comp_forget (A : SmallEtale B S hS X.1) :
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor ⋙
      Over.forget A).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      (SmallEtale.topology B S hS X.1) :=
  Functor.isContinuous_comp _ _ _ ((SmallEtale.topology B S hS X.1).over A) _

/-- The inclusion of the small Zariski site of the chart's scheme followed by the inverse of the
comparison of the two small étale sites is continuous. -/
instance isContinuous_opensToSmallEtale_comp_representedInverse (A : SmallEtale B S hS X.1) :
    ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property) ⋙
      (representedSmallEtaleEquivalence B S hS
        (chartFppfObject B S hS X A)).inverse).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A))
      (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A))) :=
  Functor.isContinuous_comp _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS X A).left.property) _

/-- The composite comparison functor of a chart is continuous from the small Zariski site of the
chart's scheme to the small étale site of `X`. -/
instance isContinuous_chartComparisonFunctor (A : SmallEtale B S hS X.1) :
    (chartComparisonFunctor B S hS X A).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS X.1) :=
  Functor.isContinuous_comp _ _ _
    (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A))) _

/-! ### The composite structure map -/

/-- The first half of the composite structure map of a chart: the comparison of structure sheaves
of the small étale site of the chart's scheme, followed by the structure map of the inverse of the
comparison of the two small étale sites. -/
noncomputable def chartComparisonRingMapZariski (A : SmallEtale B S hS X.1) :
    (chartScheme A).ringCatSheaf ⟶
      (((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property) ⋙
        (representedSmallEtaleEquivalence B S hS
          (chartFppfObject B S hS X A)).inverse).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme A))
        (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))).obj
          (chartStructureRingSheaf B S hS X A) :=
  (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS X A).left.property) ≫
    ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          (chartScheme A)
          (chartFppfObject B S hS X A).left.property).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme A))
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property)).map
      (Stacks.SheafOfModules.reindexBackSharp
        (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
        (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
        (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))

/-- The second half of the composite structure map of a chart: the two steps of the localization
of Stacks 04M0, both of which carry the identity as their structure map. -/
noncomputable def chartComparisonRingMapEtale (A : SmallEtale B S hS X.1) :
    chartStructureRingSheaf B S hS X A ⟶
      (((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor ⋙
        Over.forget A).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
        (SmallEtale.topology B S hS X.1)).obj (structureRingSheaf B S hS X) :=
  (𝟙 (chartStructureRingSheaf B S hS X A)) ≫
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1
          A).functor.sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
        ((SmallEtale.topology B S hS X.1).over A)).map
      (𝟙 ((structureRingSheaf B S hS X).over A))

/-- The composite structure map of a chart: the morphism of sheaves of rings along which the
chart restriction is the direct image of `M`. -/
noncomputable def chartComparisonRingMap (A : SmallEtale B S hS X.1) :
    (chartScheme A).ringCatSheaf ⟶
      ((chartComparisonFunctor B S hS X A).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme A))
        (SmallEtale.topology B S hS X.1)).obj (structureRingSheaf B S hS X) :=
  chartComparisonRingMapZariski B S hS X A ≫
    (((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property) ⋙
        (representedSmallEtaleEquivalence B S hS
          (chartFppfObject B S hS X A)).inverse).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme A))
        (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))).map
      (chartComparisonRingMapEtale B S hS X A)

/-- The component of the composite structure map over a Zariski open of the chart's scheme is
`AlgebraicGeometry.Space.chartSectionsRingHom`. -/
theorem chartComparisonRingMap_hom_app (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    ((chartComparisonRingMap B S hS X A).hom.app (op V)).hom
      = chartSectionsRingHom B S hS X A V := rfl

/-! ### The chart restriction as a direct image -/

/-- The chart restriction of `M` to the small Zariski site of the chart's scheme is the direct
image of `M` along the composite comparison functor, with the composite structure map. -/
theorem restrictModule_chartSchemeEtaleModule_eq_pushforward (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)
      = (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M :=
  Stacks.SheafOfModules.pushforward_four_obj
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property)
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))
    (G₃ := (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor)
    (G₄ := Over.forget A)
    (L₄ := (SmallEtale.topology B S hS X.1).over A)
    (L₅ := SmallEtale.topology B S hS X.1)
    (Q₄ := (structureRingSheaf B S hS X).over A)
    (Q₅ := structureRingSheaf B S hS X)
    (𝟙 _) (𝟙 _) M

/-- Over a Zariski open `V` of the chart's scheme, the sections of the direct image of `M` along
the composite comparison functor are the sections of `M` over the étale chart which `V` cuts out,
with scalars restricted along the composite structure map. -/
theorem chartComparisonPushforward_obj_val_obj (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M).val.obj (op V)
      = (ModuleCat.restrictScalars ((chartComparisonRingMap B S hS X A).hom.app (op V)).hom).obj
          (M.val.obj (op (openChartOfComparison B S hS X A V))) :=
  Stacks.SheafOfModules.pushforward_obj_val_obj (chartComparisonRingMap B S hS X A) M V

/-- The restriction map of the direct image of `M` along the composite comparison functor, along
an inclusion `V' ≤ V` of Zariski opens of the chart's scheme, is the restriction map of `M` along
the induced morphism of étale charts. -/
theorem chartComparisonPushforward_presheaf_map (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V) :
    ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj
        M).val.presheaf.map (homOfLE h).op
      = M.val.presheaf.map (openChartOfComparisonHom B S hS X A h).op :=
  Stacks.SheafOfModules.pushforward_obj_val_presheaf_map (chartComparisonRingMap B S hS X A) M
    (homOfLE h)

end AlgebraicGeometry.Space

end
