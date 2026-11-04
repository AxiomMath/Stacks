module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization

/-!
# One chart of the source covers the base change of every Zariski open of a chart

Let `f : Y ⟶ X` be a morphism of algebraic spaces, let `V` be an étale scheme chart of `X` and
let `W` be an étale scheme chart of `Y` covering the base change `Y ×_X V` — the chart Tag 03H7
produces for `V`.  For a Zariski open `O` of the chart's scheme, `Y ×_X openChart V O` is the
base change of the smaller chart, and Tag 03H7 applied to *it* would produce an unrelated chart
of `Y`.  This file shows that no new chart is needed: the open subscheme of `chartScheme W` that
the induced morphism `chartScheme W ⟶ chartScheme V` pulls `O` back to already covers
`Y ×_X openChart V O`, for *every* `O`.

That is the quantifier order the containment obligation of Stacks 081V needs.  A bound on the
sections of `f_* 𝒪_Y` over `openChart V O` obtained from Tag 03H7 alone is indexed by the chart
Tag 03H7 chose for `O`, so the bounds over the `#(chartScheme V).affineOpens`-many opens are
bounded by no single cardinal — taking their supremum would need the cofinality of the cutoff,
which `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` does not supply.  Here one chart `W`
serves all of them, and every bound is a bound by `chartScheme W`, whose open subschemes are no
larger.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeChartHom` and
  `AlgebraicGeometry.Space.chartBaseChangeSchemeMap` are the morphism of the big fppf category
  over `S` and the morphism of schemes `chartScheme W ⟶ chartScheme V` induced by a morphism
  `W ⟶ Y ×_X V` of the spaces-étale site.
* `AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` is the morphism from the open chart of
  `W` cut out by the preimage of `O` to the base change `Y ×_X openChart V O`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartBaseChangeOpenChartHom`: that morphism sits in a
  cartesian square over the given `W ⟶ Y ×_X V`, so it is its base change.
* `AlgebraicGeometry.Space.isCovering_chartBaseChangeOpenChartHom`: **hence it is a covering as
  soon as the given one is**, for every Zariski open `O` — the uniform statement.
* `AlgebraicGeometry.Space.exists_openChart_isCovering_chartBaseChange_openChart`: the same with
  the chart of `Y` produced rather than assumed, in the shape a size bound consumes.

## Implementation notes

The cartesian square is assembled from two squares that are already available.  The lower one is
`AlgebraicGeometry.Space.spacesBaseChange_naturality_isPullback`: naturality of the cartesian
projection of Tag 03G2 is itself cartesian, so `Y ×_X openChart V O` is the fibre product of
`openChart V O` with `Y ×_X V` over `V`.  The outer one is the Zariski square
`O ×_{chartScheme V} chartScheme W = chartBaseChangeSchemeMap ⁻¹ᵁ O`, which is
`AlgebraicGeometry.isPullback_morphismRestrict` read successively through
`AlgebraicGeometry.BigFppfOver.toScheme` (which preserves and reflects fibre products),
`CategoryTheory.yoneda` and the inclusion of the algebraic spaces into presheaves.  Cancelling
the lower square out of the outer one is `CategoryTheory.IsPullback.of_bot`, and the result is
read in the spaces-étale site by `AlgebraicGeometry.Space.isPullback_of_toSpaces`.

Nothing here needs `f` to be relatively representable, and nothing is assumed of `W` beyond the
morphism to the base change: the covering hypothesis is used only in the last step, where
surjectivity on points passes to the base change by Tag 03MH.

No `stacks` attribute is carried.  The statement is not a clause of any tag: Tag 03H7 asserts
the existence of a covering chart for a single object of the spaces-étale site, and the content
here is that one such chart can be reused along a family of Zariski opens.  It is the
containment obligation this library's big-site convention adds.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (V : SmallEtale B S hS X.1)
    {W : SmallEtale B S hS Y.1}
    (g : (comparisonFunctor B S hS Y).obj W ⟶ chartBaseChange B S hS f V)

/-! ### The chart morphism induced by a chart over a base change -/

/-- The morphism of étale charts underlying a morphism `W ⟶ Y ×_X V` of the spaces-étale site
of `Y`: the Yoneda preimage of the composite with the cartesian projection of Tag 03G2. -/
noncomputable abbrev chartBaseChangeChartHom :
    (SmallEtale.toOver B S hS Y.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V :=
  chartBaseChangeMap B S hS f V (StructuredArrow.mk g.op)

/-- The morphism of schemes `chartScheme W ⟶ chartScheme V` induced by a morphism
`W ⟶ Y ×_X V` of the spaces-étale site of `Y`. -/
noncomputable abbrev chartBaseChangeSchemeMap : chartScheme W ⟶ chartScheme V :=
  (BigFppfOver.toScheme B S hS).map (chartBaseChangeChartHom B S hS f V g)

/-- The cartesian projection of Tag 03G2 turns the given morphism to the base change into the
induced chart morphism. -/
theorem toSpaces_map_comp_projection_app :
    (SpacesEtale.toSpaces B S hS Y).map g ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V) =
      ObjectProperty.homMk (yoneda.map (chartBaseChangeChartHom B S hS f V g)) :=
  ObjectProperty.hom_ext _
    (yoneda_map_chartBaseChangeMap B S hS f V (StructuredArrow.mk g.op)).symm

/-- **The induced chart morphism is a morphism over `f`.**  Composed with the chart `V ⟶ X` it
is the chart `W ⟶ Y` followed by `f`, which is the triangle the cartesian square of Tag 03G2
provides. -/
theorem yoneda_map_chartBaseChangeChartHom_comp_hom :
    yoneda.map (chartBaseChangeChartHom B S hS f V g) ≫ V.obj.hom = W.obj.hom ≫ f.hom := by
  have hgw : (SpacesEtale.toSpaces B S hS Y).map g ≫
      ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS X).obj V)).obj.hom =
      ((comparisonFunctor B S hS Y).obj W).obj.hom :=
    ((SpacesEtale.inclusion B S hS Y).map g).w
  have h : ((SpacesEtale.toSpaces B S hS Y).map g ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V)) ≫
      ((comparisonFunctor B S hS X).obj V).obj.hom =
      ((comparisonFunctor B S hS Y).obj W).obj.hom ≫ f := by
    rw [Category.assoc, ((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS X).obj V)).w, ← Category.assoc, hgw]
  rw [toSpaces_map_comp_projection_app B S hS f V g] at h
  exact congrArg (fun k => k.hom) h

/-! ### The open chart of the covering chart cut out by a Zariski open -/

variable (O : (chartScheme V).Opens)

variable {B S hS} in
/-- **An open of an object of the big fppf site, its preimage along a morphism and the
restriction of that morphism between them form a cartesian square.**  This is
`AlgebraicGeometry.isPullback_morphismRestrict`, the functor to schemes preserving fibre
products and reflecting isomorphisms.

Nothing about charts enters: it is a statement about the open subobjects of
`AlgebraicGeometry.Space.openSub` and an arbitrary morphism `σ` of the big fppf category
over `S`.  Applied to the chart morphism induced by a morphism to a base change it is the
Zariski square `O ×_{chartScheme V} chartScheme W = chartBaseChangeSchemeMap ⁻¹ᵁ O` below;
applied to the cartesian projection of a base-changed chart it is the interchange of chart
base change with Zariski opens of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange`. -/
theorem isPullback_openSubHomOfRestrict {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    IsPullback (openSubHom A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O))
      (openSubHomOfRestrict σ O) σ (openSubHom A O) := by
  have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
  rw [toScheme_map_openSubHom, toScheme_map_openSubHom]
  exact (isPullback_morphismRestrict ((BigFppfOver.toScheme B S hS).map σ) O).flip

/-- **The base change of a Zariski open of a chart, covered by an open subscheme of the covering
chart.**  The morphism from the open chart of `W` cut out by the preimage of `O` to the base
change `Y ×_X openChart V O`: on charts it is the restriction of the induced chart morphism to
`O` and its preimage, and the lift into the fibre product is the cartesian square of
Tag 03G2. -/
noncomputable def chartBaseChangeOpenChartHom :
    (comparisonFunctor B S hS Y).obj
        (openChart B S hS Y.1 W (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O)) ⟶
      chartBaseChange B S hS f (openChart B S hS X.1 V O) :=
  ObjectProperty.homMk (Over.homMk
    (((spacesBaseChange B S hS f).isPullback
        ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O))).lift
      (ObjectProperty.homMk (yoneda.map
        (openSubHomOfRestrict (chartBaseChangeChartHom B S hS f V g) O)) :
        (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj
            (openChart B S hS Y.1 W (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O))) ⟶
          (SpacesEtale.toSpaces B S hS X).obj
            ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O)))
      ((comparisonFunctor B S hS Y).obj
        (openChart B S hS Y.1 W
          (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O))).obj.hom
      (ObjectProperty.hom_ext _ (by
        change yoneda.map (openSubHomOfRestrict (chartBaseChangeChartHom B S hS f V g) O) ≫
            yoneda.map (openSubHom ((SmallEtale.toOver B S hS X.1).obj V) O) ≫ V.obj.hom =
          (yoneda.map (openSubHom ((SmallEtale.toOver B S hS Y.1).obj W)
            (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O)) ≫ W.obj.hom) ≫ f.hom
        rw [← Category.assoc, ← yoneda.map_comp,
          openSubHomOfRestrict_comp_openSubHom (chartBaseChangeChartHom B S hS f V g) O,
          yoneda.map_comp, Category.assoc,
          yoneda_map_chartBaseChangeChartHom_comp_hom B S hS f V g, Category.assoc])))
    (((spacesBaseChange B S hS f).isPullback
        ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O))).lift_snd _ _ _))

/-- `AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` is characterised by its composite with
the cartesian projection of Tag 03G2: it is the restriction of the induced chart morphism. -/
theorem chartBaseChangeOpenChartHom_comp_projection :
    (SpacesEtale.toSpaces B S hS Y).map (chartBaseChangeOpenChartHom B S hS f V g O) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O)) =
      ObjectProperty.homMk (yoneda.map
        (openSubHomOfRestrict (chartBaseChangeChartHom B S hS f V g) O)) :=
  ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O))).lift_fst _ _ _

/-- The outer cartesian square: the Zariski square `O ×_{chartScheme V} chartScheme W` read
among algebraic spaces, with the two composites to `openChart V O` and to `V` spelled through
the cartesian projection of Tag 03G2. -/
theorem isPullback_projection_chartBaseChangeOpenChartHom :
    IsPullback
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map
        (openChartInclusion B S hS Y.1 W (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O))))
      ((SpacesEtale.toSpaces B S hS Y).map (chartBaseChangeOpenChartHom B S hS f V g O) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O)))
      ((SpacesEtale.toSpaces B S hS Y).map g ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V))
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map
        (openChartInclusion B S hS X.1 V O))) := by
  rw [chartBaseChangeOpenChartHom_comp_projection B S hS f V g O,
    toSpaces_map_comp_projection_app B S hS f V g]
  have h := (isPullback_openSubHomOfRestrict (chartBaseChangeChartHom B S hS f V g) O).map yoneda
  exact IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h.w) h

/-- The square of `AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` over the given morphism
to the base change commutes.  Both composites are morphisms into the fibre product `Y ×_X V`,
so they agree as soon as they do after the cartesian projection — which is the Zariski square —
and after the structure morphism to `Y`, which is automatic in the spaces-étale site. -/
theorem chartBaseChangeOpenChartHom_comp :
    (comparisonFunctor B S hS Y).map
          (openChartInclusion B S hS Y.1 W
            (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O)) ≫ g =
      chartBaseChangeOpenChartHom B S hS f V g O ≫
        (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O)) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS X).obj V)).hom_ext ?_ ?_
  · have hnat : (SpacesEtale.toSpaces B S hS Y).map
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O))) ≫
          (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V) =
        (spacesBaseChange B S hS f).projection.app
            ((comparisonFunctor B S hS X).obj (openChart B S hS X.1 V O)) ≫
          (SpacesEtale.toSpaces B S hS X).map
            ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O)) :=
      (spacesBaseChange B S hS f).projection.naturality _
    show ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map
          (openChartInclusion B S hS Y.1 W
            (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O))) ≫
          (SpacesEtale.toSpaces B S hS Y).map g) ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V) =
      ((SpacesEtale.toSpaces B S hS Y).map (chartBaseChangeOpenChartHom B S hS f V g O) ≫
          (SpacesEtale.toSpaces B S hS Y).map ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O)))) ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS X).obj V)
    rw [Category.assoc, Category.assoc, hnat,
      toSpaces_map_comp_projection_app B S hS f V g, ← Category.assoc,
      chartBaseChangeOpenChartHom_comp_projection B S hS f V g O]
    refine ObjectProperty.hom_ext _ ?_
    exact (congrArg yoneda.map
      (openSubHomOfRestrict_comp_openSubHom (chartBaseChangeChartHom B S hS f V g) O)).symm
  · have h₁ := ((SpacesEtale.inclusion B S hS Y).map ((comparisonFunctor B S hS Y).map
      (openChartInclusion B S hS Y.1 W
        (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O)) ≫ g)).w
    have h₂ := ((SpacesEtale.inclusion B S hS Y).map
      (chartBaseChangeOpenChartHom B S hS f V g O ≫
        (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O)))).w
    exact h₁.trans h₂.symm

/-- **The square of `AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` over the given
morphism to the base change is cartesian**, read among algebraic spaces. -/
theorem isPullback_toSpaces_chartBaseChangeOpenChartHom :
    IsPullback
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map
        (openChartInclusion B S hS Y.1 W (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O))))
      ((SpacesEtale.toSpaces B S hS Y).map (chartBaseChangeOpenChartHom B S hS f V g O))
      ((SpacesEtale.toSpaces B S hS Y).map g)
      ((SpacesEtale.toSpaces B S hS Y).map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O)))) := by
  refine IsPullback.of_bot
    (isPullback_projection_chartBaseChangeOpenChartHom B S hS f V g O) ?_
    (spacesBaseChange_naturality_isPullback B S hS f
      ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O))).flip
  rw [← Functor.map_comp, ← Functor.map_comp, chartBaseChangeOpenChartHom_comp B S hS f V g O]

/-- **The square of `AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` over the given
morphism to the base change is cartesian**, read in the spaces-étale site of `Y`: the open chart
of `W` cut out by the preimage of `O` *is* the base change of `W` along the inclusion of
`Y ×_X openChart V O` into `Y ×_X V`. -/
theorem isPullback_chartBaseChangeOpenChartHom :
    IsPullback
      ((comparisonFunctor B S hS Y).map
        (openChartInclusion B S hS Y.1 W (chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O)))
      (chartBaseChangeOpenChartHom B S hS f V g O) g
      ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS X).map (openChartInclusion B S hS X.1 V O))) :=
  isPullback_of_toSpaces B S hS
    (isPullback_toSpaces_chartBaseChangeOpenChartHom B S hS f V g O)

/-- **The uniform covering statement.**  If `W` covers the base change `Y ×_X V`, then for
*every* Zariski open `O` of `chartScheme V` the open chart of `W` cut out by the preimage of `O`
covers `Y ×_X openChart V O`.

Surjectivity on points passes to a base change by Tag 03MH, and the square of
`AlgebraicGeometry.Space.chartBaseChangeOpenChartHom` is cartesian.  The point is that the chart
`W` does not depend on `O`: Tag 03H7 applied to `Y ×_X openChart V O` would produce a chart of
`Y` with no relation to `W`, and the bounds the resulting coverings give are then bounded by no
single cardinal. -/
theorem isCovering_chartBaseChangeOpenChartHom
    (hg : SpacesEtale.IsCovering B S hS Y
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩) :
    SpacesEtale.IsCovering B S hS Y
      ⟨chartBaseChange B S hS f (openChart B S hS X.1 V O),
        PreZeroHypercover.singleton.{u + 1}
          (chartBaseChangeOpenChartHom B S hS f V g O)⟩ :=
  SpacesEtale.isCovering_singleton_of_isSurjective B S hS
    (chartBaseChangeOpenChartHom B S hS f V g O)
    (isSurjective_of_isPullback B S hS
      (isPullback_toSpaces_chartBaseChangeOpenChartHom B S hS f V g O)
      (fun x => ⟨(hg x).choose_spec.choose, (hg x).choose_spec.choose_spec⟩))

/-- **One chart of `Y` covers the base change of every Zariski open of a chart of `X`.**  There
is an étale scheme chart `W` of `Y` and, for every Zariski open `O` of `chartScheme V`, a Zariski
open `Q` of `chartScheme W` whose open chart covers `Y ×_X openChart V O`.

This is `AlgebraicGeometry.Space.isCovering_chartBaseChangeOpenChartHom` with the chart produced
by Tag 03H7 rather than assumed.  The order of the quantifiers is the content: `W` is chosen
before `O`, so a bound by `chartScheme W` bounds every member of the family at once, every
`chartScheme (openChart W Q)` being an open subscheme of `chartScheme W`. -/
theorem exists_openChart_isCovering_chartBaseChange_openChart :
    ∃ W : SmallEtale B S hS Y.1, ∀ O : (chartScheme V).Opens,
      ∃ (Q : (chartScheme W).Opens)
        (gO : (comparisonFunctor B S hS Y).obj (openChart B S hS Y.1 W Q) ⟶
          chartBaseChange B S hS f (openChart B S hS X.1 V O)),
        SpacesEtale.IsCovering B S hS Y
          ⟨chartBaseChange B S hS f (openChart B S hS X.1 V O),
            PreZeroHypercover.singleton.{u + 1} gO⟩ := by
  obtain ⟨W, g, -, -, hg⟩ :=
    exists_etaleChart_singleton_covering B S hS Y (chartBaseChange B S hS f V)
  exact ⟨W, fun O => ⟨chartBaseChangeSchemeMap B S hS f V g ⁻¹ᵁ O,
    chartBaseChangeOpenChartHom B S hS f V g O,
    isCovering_chartBaseChangeOpenChartHom B S hS f V g O hg⟩⟩

end AlgebraicGeometry.Space

end
