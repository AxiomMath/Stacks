module

public import StacksFrontier.AlgebraicGeometry.OpenImmersionAlgebraBridges.AlgebraPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison

/-!
# The chart restriction of an algebra sheaf against a transition map of charts

The construction of Stacks 081V — the relative spectrum of a quasi-coherent algebra over an
algebraic space — restricts the algebra to an étale scheme chart, forms the scheme-level relative
spectrum there, and glues.  `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartRestriction`
supplies the restriction to *one* chart, and records that what the gluing needs beyond it is the
compatibility of that restriction with the transition maps of an étale presentation: the
restriction `𝒜|_V` compared, along a morphism of charts `g : W ⟶ V`, with `𝒜|_W`.  That is the
algebra-level counterpart of Stacks 03M3, and this file supplies it.

The comparison is the one that exists for an arbitrary morphism of charts, in the direct-image
direction: a morphism `𝒜|_V ⟶ (chartSchemeMap g)_* 𝒜|_W` of sheaves of algebras on the chart
scheme of `V`.  Its inverse-image transpose is an isomorphism exactly for the quasi-coherent
algebras, which is the cartesianness of Descent, Proposition 03DX together with Stacks 03LY —
not Stacks 03M0 — and is *not* proved here; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensRestrict`: the morphism of étale charts of `F` induced by
  a morphism of charts `g : V ⟶ U` and a Zariski open `O` of the larger chart's scheme — the
  restriction `chartSchemeMap g ∣_ O` of the underlying morphism of schemes to `O` and its
  preimage — in the reading of the opens of a chart as charts that
  `AlgebraicGeometry.Space.chartOpens` uses, and
  `AlgebraicGeometry.Space.chartOpensRestrictNatTrans` the natural transformation
  `Opens.map (chartSchemeMap g).base ⋙ chartOpens V ⟶ chartOpens U` it assembles into.
* `AlgebraicGeometry.Space.chartOpensPushforwardTransition` is **the transition comparison of
  the chart restrictions of a sheaf of commutative rings**, natural in the sheaf.
* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition` is **the transition
  comparison of the chart restrictions of a sheaf of `𝒪_X`-algebras** — the counterpart of
  Stacks 03M3 the construction of Stacks 081V needs — and
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransitionNatTrans` is it as a
  natural transformation of functors on the algebra sheaves, which is the form glueing data
  consumes.

## Main results

* `AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict`: the morphism of schemes
  underlying `AlgebraicGeometry.Space.chartOpensRestrict` is `chartSchemeMap g ∣_ O`, on the
  nose.
* `AlgebraicGeometry.Space.chartStructureSheafIso_inv_comp_chartOpensPushforwardTransition`:
  **the transition comparison at the structure sheaf is the comorphism of the chart
  transition.**  This is the one piece of scheme geometry the algebra-level transition needs,
  and it is what makes the comparison respect the two algebra structure maps.
* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_app`: on sections over a
  Zariski open `O` of the larger chart, the transition is the restriction map of `𝒜` along
  `AlgebraicGeometry.Space.chartOpensRestrict` — an equality of terms.

## Implementation notes

**Why the direct image is the one already in the tree.**  The target of the comparison is
`Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap g)`, the direct image of
algebra sheaves along an arbitrary morphism of schemes, which is
`CategoryTheory.Under.post` of the direct image of sheaves of commutative rings followed by
`CategoryTheory.Under.map` of the comorphism.  Nothing about it is specific to open immersions,
despite the file it is proved fully faithful in; and the comorphism itself is
`Stacks.OpenImmersionAlgebraBridges.structureSheafHom`, which is `⟨g.c⟩` spelled as a definition
because that anonymous constructor is not type-correct at instance transparency.

**Why this comparison needs no sheafification, and the module-level one does.**  The chart
restriction of a sheaf of commutative rings is the continuous pushforward along
`AlgebraicGeometry.Space.chartOpens`, so restricting along a composite of index functors is a
composite of restrictions on the nose, and the comparison is the map on sections induced by
`AlgebraicGeometry.Space.chartOpensRestrictNatTrans` and nothing else.  The module-level
counterpart `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison` has to pass a
presheaf-level comparison through the Zariski sheafification adjunction, which is why it is
longer.

**What is reused rather than rebuilt.**  The morphism of the big fppf category over `S` from a
Zariski open of the smaller chart to one of the larger is
`AlgebraicGeometry.Space.chartOpenOverRestrict`, already in the tree in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare` and strictly more general than what
is wanted here: it takes an arbitrary morphism between the big-fppf objects of charts of two
*different* presheaves, whereas a chart transition supplies one between charts of the same
presheaf, lying over `F`.  Only the triangle over `F` is added, and
`AlgebraicGeometry.Space.chartOpenOverRestrict_comp_ι` discharges it.

**Why the chart-level transition is rebuilt here rather than transported.**
`AlgebraicGeometry.Space.openChartRestrictNatTrans` is the same natural transformation for the
*other* index functor `AlgebraicGeometry.Space.openChartFunctor`, and the two index functors are
equal, by `AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor`.  Transporting along that
equality does typecheck — `CategoryTheory.eqToHom` of it composes with the natural
transformation in the functor category — but the components are then
`eqToHom ≫ openChartRestrict g O ≫ eqToHom`, and
`AlgebraicGeometry.Space.chartStructureSheafIso_inv_comp_chartOpensPushforwardTransition` no
longer reduces to its one scheme-level input: elaborating that proof against the transported
transformation exhausts the 200000-heartbeat limit at `whnf`.  Built directly, the component is
`chartSchemeMap g ∣_ O` by `AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict`, which is
`rfl`, and the proof is one `exact`.  The two constructions agree — both are
`AlgebraicGeometry.morphismRestrict` of the chart morphism, read through the two spellings of a
Zariski open of a chart as a chart — and this file does not state that they do, since the
statement would need exactly the transport it exists to avoid.

**What is not proved here.**  Three things, in increasing order of distance.

* The comparison is *not* claimed to be an isomorphism in its inverse-image form, and it is not
  one for a general algebra sheaf: cartesianness along étale chart morphisms holds exactly for
  the quasi-coherent ones — the cartesianness of Descent, Proposition 03DX together with the
  identification of the chart restriction with an inverse image, Stacks 03LY, and **not**
  Stacks 03M0, which is the characterisation of quasi-coherence itself.  Transporting those
  conditions needs the identification of the slice of the small étale site at a chart with the
  small étale site of the chart (Stacks 04M0), recorded as missing in the implementation notes
  of `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart`.  The same caveat is
  recorded for the module-level comparison in
  `StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison`.
* The *cocycle laws* in the chart morphism are not stated **here**; they are stated and proved in
  `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCocycle`, as
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_id` and
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_comp`.  Neither needs
  a transport carrying a `CategoryTheory.eqToHom` on the preimage of the open: for the
  two functors `chartSchemeMap` is composed of, both laws hold by `rfl`
  (`AlgebraicGeometry.Space.chartSchemeMap_id`, `AlgebraicGeometry.Space.chartSchemeMap_comp`),
  the preimage of an open along a composite of morphisms of schemes is the iterated preimage by
  `rfl`, and `Stacks.AffineAlgebraEquivalence.algebraPushforward` of a composite *is* the
  composite of the direct images, also by `rfl`
  (`Stacks.AffineAlgebraEquivalence.algebraPushforward_comp`; the docstring of
  `Stacks.AffineAlgebraEquivalence.algebraPullbackComp` already asserted as much).  Both cocycle
  laws are therefore equations between morphisms of definitionally equal types, with no
  transport in either statement.
* Consequently no glueing datum is assembled and **nothing here carries Stacks 081V**, nor
  Stacks 03M3: this is one input to the construction of the relative spectrum over an algebraic
  space, and the essential-surjectivity clause
  `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff` is untouched.
  Neither fullness nor faithfulness of
  `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` is addressed.

**Related results.**  Stacks 03M3 is formalized as a full equivalence:
`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase` and
`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`, in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence`, carry
`@[stacks 03M3]` for the equivalence `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` itself, for a target which
is an algebraic space.  The base-change clause of Stacks 01SA is proved by
`Stacks.AffineAlgebraEquivalence.isQuasicoherentAlgebraPullback`,
`Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom` and
`Stacks.AffineAlgebraEquivalence.affineAlgebraAntiEquivalence`, in
`StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.GeneralBaseChange`.  Neither is an
input this file uses.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### A morphism of charts, restricted to an open of the target and its preimage -/

/-- **The morphism of étale charts of `F` induced by a morphism of charts and a Zariski open of
the larger chart**, in the reading of the opens of a chart as charts of `F` that
`AlgebraicGeometry.Space.chartOpens` uses.

The morphism of the site underneath it is
`AlgebraicGeometry.Space.chartOpenOverRestrict`, which is already in the tree, for an arbitrary
morphism between the big-fppf objects of two charts of two presheaves; the morphism of charts
over `F` here is its special case at the morphism underlying `g`, together with the triangle
over `F`. -/
def chartOpensRestrict {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    (chartOpens B S hS V).obj (chartSchemeMap g ⁻¹ᵁ O) ⟶ (chartOpens B S hS U).obj O :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (chartOpenOverRestrict B S hS V U ((SmallEtale.toOver B S hS F).map g) O) (by
      change yoneda.map
            (chartOpenOverRestrict B S hS V U ((SmallEtale.toOver B S hS F).map g) O) ≫
          yoneda.map (chartOpenOverι B S hS U O) ≫ U.obj.hom =
        yoneda.map (chartOpenOverι B S hS V (chartSchemeMap g ⁻¹ᵁ O)) ≫ V.obj.hom
      rw [← yoneda_map_toOver_map_comp_hom g, ← Category.assoc, ← Category.assoc,
        ← yoneda.map_comp, ← yoneda.map_comp,
        chartOpenOverRestrict_comp_ι B S hS V U ((SmallEtale.toOver B S hS F).map g) O]))

/-- The underlying morphism of schemes of
`AlgebraicGeometry.Space.chartOpensRestrict` is the restriction of the chart morphism to the
open and its preimage.  This is an equality of terms, not a transport: the reading of a Zariski
open of a chart as a chart of `F` keeps the open subscheme itself as the underlying scheme. -/
theorem chartSchemeMap_chartOpensRestrict {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    chartSchemeMap (chartOpensRestrict B S hS g O) = chartSchemeMap g ∣_ O :=
  rfl

/-- Naturality of `AlgebraicGeometry.Space.chartOpensRestrict` in the open. -/
theorem chartOpensRestrict_naturality {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O O' : (chartScheme U).Opens} (i : O ⟶ O') :
    (chartOpens B S hS V).map ((Opens.map (chartSchemeMap g).base).map i) ≫
        chartOpensRestrict B S hS g O' =
      chartOpensRestrict B S hS g O ≫ (chartOpens B S hS U).map i := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change (chartScheme V).homOfLE ((Opens.map (chartSchemeMap g).base).map i).le ≫
      (chartSchemeMap g ∣_ O') =
    (chartSchemeMap g ∣_ O) ≫ (chartScheme U).homOfLE i.le
  rw [← cancel_mono O'.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- **The transition natural transformation of the index functors of the chart restriction.**
For a morphism `g : V ⟶ U` of étale charts of `F`, the Zariski opens of the larger chart's
scheme, read as charts of `F` through their preimages in the smaller chart, map naturally to the
Zariski opens of the larger one. -/
def chartOpensRestrictNatTrans {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    Opens.map (chartSchemeMap g).base ⋙ chartOpens B S hS V ⟶ chartOpens B S hS U where
  app O := chartOpensRestrict B S hS g O
  naturality {_O _O'} i := chartOpensRestrict_naturality B S hS g i

/-! ### The transition comparison of the chart restrictions of a sheaf of rings -/

variable {X : AlgebraicSpaces B S hS}

/-- **The transition comparison of the chart restrictions of a sheaf of commutative rings on the
small étale site of `X`.**  For a morphism `g : W ⟶ V` of étale scheme charts of `X` the
restriction of `𝒜` to the larger chart maps to the direct image along
`AlgebraicGeometry.Space.chartSchemeMap` of its restriction to the smaller one, naturally in
`𝒜`.

Unlike the module-level counterpart
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison`, no sheafification stands
in the way: the chart restriction of a sheaf of rings is the continuous pushforward along
`AlgebraicGeometry.Space.chartOpens`, so the comparison is the map on sections induced by
`AlgebraicGeometry.Space.chartOpensRestrictNatTrans` and nothing else, and its naturality in
`𝒜` is the naturality of that map. -/
def chartOpensPushforwardTransition {V W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    chartOpensPushforward B S hS V ⟶
      chartOpensPushforward B S hS W ⋙
        TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base where
  app A := ⟨Functor.whiskerRight (NatTrans.op (chartOpensRestrictNatTrans B S hS g)) A.obj⟩
  naturality {_A _C} f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    exact (f.hom.naturality ((chartOpensRestrictNatTrans B S hS g).app O.unop).op).symm

/-- Naturality of `AlgebraicGeometry.Space.chartOpensPushforwardTransition`, with the composite
functor on the right written out as the two restrictions one after the other.  The two readings
are definitionally equal; this one is the form the algebra-level transition is assembled over,
where the direct image of the structure map of the algebra has to be split off. -/
theorem chartOpensPushforward_map_comp_chartOpensPushforwardTransition_app
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    {A C : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (f : A ⟶ C) :
    (chartOpensPushforward B S hS V).map f ≫
        (chartOpensPushforwardTransition B S hS g).app C =
      (chartOpensPushforwardTransition B S hS g).app A ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base).map
          ((chartOpensPushforward B S hS W).map f) :=
  (chartOpensPushforwardTransition B S hS g).naturality f

/-- **The transition comparison carries the structure sheaf of a chart to the comorphism of the
chart transition.**  Under the identifications
`AlgebraicGeometry.Space.chartStructureSheafIso` of the chart restrictions of `𝒪_X` with the
structure sheaves of the two chart schemes, the transition comparison at `𝒪_X` *is* the
comorphism `𝒪_V ⟶ (chartSchemeMap g)_* 𝒪_W` of the morphism of schemes underlying the chart
transition.

This is the one piece of scheme geometry the algebra-level transition needs, and it is
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` applied at each
Zariski open of the larger chart: by
`AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict` the comparison at the open `O` is
pullback of global functions along `chartSchemeMap g ∣_ O`, which is exactly what that lemma
compares with the section map of the chart transition at `O`. -/
theorem chartStructureSheafIso_inv_comp_chartOpensPushforwardTransition
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    (chartStructureSheafIso B S hS V).inv ≫
        (chartOpensPushforwardTransition B S hS g).app (structureSheaf B S hS X.1 X.2) =
      Stacks.OpenImmersionAlgebraBridges.structureSheafHom (chartSchemeMap g) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base).map
          (chartStructureSheafIso B S hS W).inv := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext O
  obtain ⟨O⟩ := O
  exact Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict (chartSchemeMap g) O

/-! ### The transition comparison of the chart restrictions of an algebra sheaf -/

/-- **The algebra-level transition compatibility of the chart restriction: the counterpart of
Stacks 03M3 that the construction of Stacks 081V needs.**

For a sheaf `𝒜` of `𝒪_X`-algebras on the small étale site of an algebraic space `X` and a
morphism `g : W ⟶ V` of étale scheme charts of `X`, the restriction `𝒜|_V` of
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartScheme` maps to the direct image along
`chartSchemeMap g` of `𝒜|_W`, as sheaves of algebras on the chart scheme of `V`.  The direct
image is `Stacks.AffineAlgebraEquivalence.algebraPushforward`, the direct image of algebra
sheaves along an arbitrary morphism of schemes.

The underlying map of sheaves of rings is
`AlgebraicGeometry.Space.chartOpensPushforwardTransition`; that it respects the two structure
maps is
`AlgebraicGeometry.Space.chartStructureSheafIso_inv_comp_chartOpensPushforwardTransition`
together with naturality of the comparison in the sheaf of rings. -/
def AlgebraSheaf.restrictToChartSchemeTransition (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    A.restrictToChartScheme B S hS V ⟶
      (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap g)).obj
        (A.restrictToChartScheme B S hS W) :=
  Under.homMk ((chartOpensPushforwardTransition B S hS g).app A.right) (by
    change (chartStructureSheafIso B S hS V).inv ≫
          (chartOpensPushforward B S hS V).map A.hom ≫
          (chartOpensPushforwardTransition B S hS g).app A.right =
        Stacks.OpenImmersionAlgebraBridges.structureSheafHom (chartSchemeMap g) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base).map
            ((chartStructureSheafIso B S hS W).inv ≫
              (chartOpensPushforward B S hS W).map A.hom)
    exact ((congrArg (fun k => (chartStructureSheafIso B S hS V).inv ≫ k)
          (chartOpensPushforward_map_comp_chartOpensPushforwardTransition_app
            B S hS g A.hom)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫
                (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base).map
                  ((chartOpensPushforward B S hS W).map A.hom))
              (chartStructureSheafIso_inv_comp_chartOpensPushforwardTransition
                B S hS g)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun k =>
                  Stacks.OpenImmersionAlgebraBridges.structureSheafHom
                    (chartSchemeMap g) ≫ k)
                ((TopCat.Sheaf.pushforward CommRingCat.{u}
                  (chartSchemeMap g).base).map_comp _ _).symm))))))

/-- The underlying map of sheaves of rings of the algebra-level transition is the transition
comparison of the chart restrictions of the underlying sheaf of rings. -/
@[simp]
theorem AlgebraSheaf.restrictToChartSchemeTransition_right
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) {V W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    (A.restrictToChartSchemeTransition B S hS g).right =
      (chartOpensPushforwardTransition B S hS g).app A.right :=
  rfl

/-- **On sections, the transition of the chart restrictions is the restriction map of `𝒜` along
the chart morphism `AlgebraicGeometry.Space.chartOpensRestrict`.**  Over a Zariski open `O` of
the larger chart's scheme it carries a section of `𝒜|_V` over `O` to its pullback along the
morphism of étale charts of `X` that restricts `g` to `O` and its preimage — which is what the
target, the sections of `𝒜|_W` over the preimage of `O`, is by
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartScheme_sections`.

This is the concrete content of the transition compatibility, and it is an equality of terms. -/
theorem AlgebraSheaf.restrictToChartSchemeTransition_app
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (O : (chartScheme V).Opens) :
    (A.restrictToChartSchemeTransition B S hS g).right.hom.app (op O) =
      A.right.obj.map (chartOpensRestrict B S hS g O).op :=
  rfl

/-- **The algebra-level transition compatibility of the chart restriction, as a natural
transformation.**  For a morphism `g : W ⟶ V` of étale scheme charts of `X`, restriction to the
larger chart followed by nothing, and restriction to the smaller chart followed by direct image
along `chartSchemeMap g`, are two functors from the sheaves of `𝒪_X`-algebras to the sheaves of
algebras on the chart scheme of `V`, and the transition compatibility is a natural
transformation between them.

This is the form the glueing data of Stacks 081V consumes: the transition is not merely a
morphism attached to each algebra sheaf but one natural in it, so it may be applied to a
morphism of algebra sheaves and to the structure map in particular. -/
def AlgebraSheaf.restrictToChartSchemeTransitionNatTrans
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) :
    AlgebraSheaf.restrictToChartSchemeFunctor B S hS V ⟶
      AlgebraSheaf.restrictToChartSchemeFunctor B S hS W ⋙
        Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap g) where
  app A := A.restrictToChartSchemeTransition B S hS g
  naturality {_A _C} f := by
    apply Under.UnderMorphism.ext
    exact (chartOpensPushforwardTransition B S hS g).naturality f.right

end AlgebraicGeometry.Space

end
