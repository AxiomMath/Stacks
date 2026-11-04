module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFinitePresentationProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# Projective sections of a flat finitely presented module along a fibre of an algebraic space

Tag 0CVZ asserts, for a morphism `f : X ⟶ Y` of algebraic spaces over `S`, a quasi-coherent
`𝒪_X`-module `𝓕` and a point `y ∈ |Y|` with fibre `F = f^{-1}({y}) ⊂ |X|`, under the three
hypotheses that `f` be of finite presentation, `𝓕` be of finite presentation and `𝓕` be flat
over `Y` at every point of `F`, the existence of a commutative diagram
```
X ←—— X'
|      |
↓      ↓
Y ←—— Y'
```
whose horizontal arrows `g : X' → X` and `h : Y' → Y` are étale, in which `X'` and `Y'` are
affine, with a point `y' ∈ |Y'|` over `y` and with `F ⊂ g(|X'|)`, such that `Γ(X', g^*𝓕)` is a
projective `Γ(Y', 𝒪_{Y'})`-module.

This is the fibrewise companion of Tag 0CVY, which is the same conclusion at a single point of
`|X|` and is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFinitePresentationProjectiveSections.lean`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isCompact_setFibre_of_isQuasiCompact`: the set-theoretic fibre of a
  quasi-compact morphism of algebraic spaces over a field-valued point of the target is a
  quasi-compact subset of the point space of the source.
* `AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_along_fibre`: the diagram of the
  conclusion of Tag 0CVZ, **unconditionally**. A commuting square of affine étale scheme charts
  over `f`, through a point of the target chart over `y`, whose source chart covers the whole
  fibre `F`. Only quasi-compactness of `f` is assumed; the projectivity of the sections, which
  is the only clause needing the case of schemes, is not asserted.
* `AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections_along_fibre`: the case
  of schemes, Tag 05KW, read inside the big fppf site.
* `AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_along_fibre`: the
  full conclusion of Tag 0CVZ, projectivity of the sections included, **unconditionally**, with
  the tag's conditions (2) and (3) on the module in their étale-chartwise form.
* `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_of_isFlatOverAtPoint`: Stacks 05VU read
  at an arbitrary point of an arbitrary chart square — flatness over the target at a point of
  `|X|` on one chart square gives it on all of them.
* `Space.exists_isAffine_etale_charts_projective_sections_along_fibre_of_isFlatOverAtPoint`:
  the same conclusion from the tag's own hypotheses throughout — `𝓕` quasi-coherent and of
  finite presentation on the small étale site of `X`, and condition (3) in the some-chart form
  which Stacks 05VV gives it. No chartwise hypothesis on the module appears.

## Implementation notes

### The reduction to the case of schemes

The source proves Tag 0CVZ in one sentence: *as formulated this lemma immediately reduces to
the case of schemes, which is More on Flatness, Lemma 05KW*. That reduction is what is proved
here, and unlike at a single point it has content: a single affine étale chart of `X` must be
found whose image contains the **whole** fibre `F`.

It is produced by base change, and this is the whole of
`AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_along_fibre`. An affine étale chart
`b : V ⟶ Y` of the target through `y` is chosen first
(`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`), and `X` is pulled back along it
to `W = X ×_Y V`; the first projection is étale, being a base change of `b`, and the second is
quasi-compact, being a base change of `f`. The fibre of `W → V` over the chart point is
therefore a quasi-compact subset of `|W|` — this is
`AlgebraicGeometry.Space.isCompact_setFibre_of_isQuasiCompact`, read off from Tag 03H4 through
the field fibre `W ×_V Spec κ` — and
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact` covers it by a single affine
étale chart `Z` of `W`. The composite `Z ⟶ W ⟶ X` is an étale chart of `X` whose image contains
`F`, because a point of `F` lifts to `W` over the chart point by Tag 03H4 and then to `Z`; and
`Z ⟶ W ⟶ V` is a morphism of the site by fullness of Yoneda, giving the commuting square of
étale charts which the chartwise hypotheses on `f` and on `𝓕` are stated over. Both charts
being affine, local finite presentation of the morphism of schemes upgrades to finite
presentation, which is what the case of schemes asks for.

The unconditional statement records the covering of `F` twice: once as the containment
`F ⊂ g(|X'|)` of the tag, and once in the sharpened form which the construction actually
produces and which the case of schemes consumes — every point of `F` is the image of a point of
the source chart lying over `y'`. The same sharpening appears at the scheme level in
`AlgebraicGeometry.exists_elementary_pointed_projective_cover`.

Unlike the companion `AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_at_point` for
Tag 0CVY, which is hypothesis-free, quasi-compactness of `f` is genuinely needed here: it is
what makes `F` quasi-compact, and without it no single affine chart need cover `F`. It is part
of hypothesis (1) of the tag.

### The case of schemes inside the site

The case of schemes is Tag 05KW,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre` of
`StacksFrontier/AlgebraicGeometry/Etale/ElementaryNeighborhood/ProjectiveSectionsAlongFibre.lean`,
and it is read inside the big fppf site by
`AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections_along_fibre`: for a
morphism `h : D ⟶ E` of the site whose morphism of schemes is of finite presentation, a
quasi-coherent `𝒪_D`-module `G` of finite presentation and a point `ε` of `E` at which `G` is
flat over `E` along the whole fibre, there are étale morphisms `p : D' ⟶ D` and `q : E' ⟶ E` of
the site with `D'` and `E'` affine, a morphism `k : D' ⟶ E'` with `k ≫ q = p ≫ h`, a point of
`E'` over `ε` and the fibre `h^{-1}(ε)` inside the image of `p`, such that `Γ(D', p^*G)` is
projective over `Γ(E', 𝒪_{E'})`.

The only thing to supply is the passage from the schemes Tag 05KW produces to objects of the
site. A scheme is an object of the big fppf site exactly when
`AlgebraicGeometry.BigFppfSite.Contains` holds of it, that is when its
`AlgebraicGeometry.Scheme.size` is below the site's cutoff, and both schemes Tag 05KW produces
— the elementary étale neighbourhood of `ε` and the affine scheme étale over `D` covering the
fibre — are **affine**, hence quasi-compact, and étale, hence locally of finite type, over a
scheme of the site. So Stacks 04T7,
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`, bounds their size by the size of
`D` respectively of `E` and both are contained. Affineness of `D` and of `E` is not needed, and
neither is the *elementarity* of the neighbourhood `E' ⟶ E` which Tag 05KW also supplies.

This is the same route as for Tag 0CVY, where it is
`AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections`.

### The tag's conditions (2) and (3) on the module

The tag's hypotheses on `𝓕` are that it be a quasi-coherent sheaf on `X`, that it be of finite
presentation, and that it be flat over `Y` at the points of `F`. Each of the three is a
condition on `X` itself, and each has a chartwise surrogate in this development; both readings
are stated, against the same tag, and the relation between them is proved in each case rather
than assumed.

The source's reading is the site one. Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`
(Stacks 03DL, and clause (1) of Stacks 03M0). Finite presentation is
`SheafOfModules.IsFinitePresentationOnSite`: Stacks 05VR defines the properties of a module on
an algebraic space, finite presentation among them (item (l)), as the intrinsic properties of a
module on the ringed site `(X_étale, 𝒪_X)`. Flatness over `Y` at a point of `|X|` is
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, the *some*-chart-square condition (1) of
Stacks 05VU, which is what Stacks 05VV's definition at a point refers to.

`Space.exists_isAffine_etale_charts_projective_sections_along_fibre_of_isFlatOverAtPoint` is
stated at exactly those three, with no chartwise hypothesis anywhere. It reduces to the
chartwise statement by three transfers, all of them theorems here:

* quasi-coherence, by `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`;
* finite presentation, by
  `AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`, which asks
  nothing of the module beyond finite presentation on the small étale site;
* flatness, by Stacks 05VU itself, which this development proves
  (`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`): both the some-chart
  and the every-chart condition at a point are membership of that point in the relative flat
  locus of Stacks 0DLR, which names no chart. That step is
  `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_of_isFlatOverAtPoint`.

`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_along_fibre` keeps the
chartwise reading of all three, and is kept because it is not implied by the site statement and
does not imply it: its quasi-coherence and finite-presentation hypotheses are weaker (they are
the conclusions of the two transfers above, and quasi-coherence chartwise is clause (4) of
Stacks 03M0), while its flatness hypothesis is stronger (every chart square rather than some).
A consumer holding only chart data uses it; a consumer reading the source uses the other.

### Why the module appears as a pullback rather than as a restriction to a chart

As in Tag 0CVY, the conclusion names `Γ(X', g^*𝓕)` as `Γ((Scheme.Modules.pullback p) (𝓕|_Z), ⊤)`,
where `Z` is the étale chart of `X` which `g` factors through and `𝓕|_Z` is
`AlgebraicGeometry.Space.restrictToChart`. That is forced: `restrictToChart` has no
functoriality in the chart in this development, so the pullback spelling is the only one in
which the module of the conclusion can be named. It is the faithful one: `g` is the composite
`X' → Z → X`, and the sections of the pullback of `𝓕|_Z` along `X' → Z` are the sections of
`g^*𝓕`.

## References

* [Stacks Project, Tag 0CVZ](https://stacks.math.columbia.edu/tag/0CVZ)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The fibre of a quasi-compact morphism is quasi-compact.** For a quasi-compact morphism
`f : X ⟶ Y` of algebraic spaces over `S` and a field-valued point `p` of `Y`, the set-theoretic
fibre `f^{-1}({y}) ⊂ |X|` over the point `y` represented by `p` is a quasi-compact subset of the
point space of `X`.

The fibre is the image of the point space of the field fibre `X ×_Y Spec κ` by Tag 03H4, that
field fibre is a quasi-compact algebraic space because `Spec κ` is one and `f` is quasi-compact,
and the image of a quasi-compact space under a continuous map is quasi-compact. -/
theorem isCompact_setFibre_of_isQuasiCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f) (p : FieldValuedPoint B S hS Y) :
    IsCompact (setFibre B S hS f p) := by
  have hspec : IsAffine ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have halg : IsAlgebraicSpace B S hS (fieldFibre B S hS f p) :=
    isAlgebraicSpace_pullback B S hS f (yonedaEquiv.symm p.value) hX
      (isAlgebraicSpace_yoneda B S hS p.siteObject) hY
  have hqcspace : IsQuasiCompactSpace B S hS (fieldFibre B S hS f p) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry (yonedaEquiv.symm p.value) f)
      (hf (yoneda.obj p.siteObject) (isAlgebraicSpace_yoneda B S hS p.siteObject)
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS p.siteObject hspec)
        (yonedaEquiv.symm p.value))
  have : CompactSpace (points B S hS (fieldFibre B S hS f p)) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS halg hqcspace
  rw [← range_pointsMap_fst_fieldFibre B S hS f p]
  exact isCompact_range (continuous_pointsMap B S hS _)

/-- **Stacks Project, Tag 0CVZ: the diagram of the conclusion.** Let `f : X ⟶ Y` be a
quasi-compact morphism of algebraic spaces over `S` and let `y` be a point of `|Y|`. Then there
is a commuting square of étale scheme charts

```
X ←—— U
|     |
↓     ↓
Y ←—— V
```

whose two charts `U` and `V` are **affine**, together with a point `y'` of `|V|` lying over `y`,
such that the fibre `F = f^{-1}({y})` is contained in the image of `|U| → |X|`. Moreover every
point of `F` is the image of a point of `|U|` lying over `y'`.

This is the diagram of Tag 0CVZ, produced with none of the tag's hypotheses on the module and
with only quasi-compactness of `f`, which is part of the tag's hypothesis (1) and is what makes
`F` quasi-compact. What Tag 0CVZ adds to it is the projectivity of `Γ(U, 𝓕|_U)` over
`Γ(V, 𝒪_V)` after a further shrinking, which is the case of schemes, Tag 05KW; that is
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_along_fibre`.

The clauses after affineness are, in order: the square of charts commutes over `f`; the chart
point lies over `y`; the fibre is contained in the image of the source chart; and the sharpened
form of that containment, by points of the source chart lying over `y'`. -/
@[stacks 0CVZ "the affine étale diagram covering the fibre — affine étale charts of the source \
and of the target with a morphism between them over f, through a point of the target chart \
over y and with the source chart covering the fibre — and nothing of the projectivity of the \
sections, which is the case of schemes, Tag 05KW"]
theorem exists_isAffine_etale_chart_square_along_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f) (y : points B S hS Y) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (k : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (y' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj V))),
      IsAffine (chartScheme U) ∧ IsAffine (chartScheme V) ∧
        U.obj.hom ≫ f = yoneda.map k ≫ V.obj.hom ∧
        pointsMap B S hS _ V.obj.hom y' = y ∧
        {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
          Set.range (pointsMap B S hS _ U.obj.hom) ∧
        ∀ x : points B S hS X, pointsMap B S hS X f x = y →
          ∃ x' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)),
            pointsMap B S hS _ U.obj.hom x' = x ∧
            pointsMap B S hS _ (yoneda.map k) x' = y' := by
  classical
  -- An affine étale chart of the target through `y`, and a field-valued representative of the
  -- chart point.
  obtain ⟨V₀, b, hV₀aff, hbE, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  obtain ⟨pv, hpv⟩ := Quot.exists_rep v
  have hpvc : pv.class B S hS (yoneda.obj V₀) = v := hpv
  -- The base change of the chart along `f`.
  have sq : IsPullback (pullback.fst f b) (pullback.snd f b) f b := IsPullback.of_hasPullback f b
  have hW : IsAlgebraicSpace B S hS (pullback f b) :=
    isAlgebraicSpace_pullback B S hS f b hX (isAlgebraicSpace_yoneda B S hS V₀) hY
  have hpr₁E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst f b) :=
    presheaf_of_isPullback B S hS sq.flip hbE
  have hpr₂qc : IsQuasiCompact B S hS (pullback.snd f b) :=
    isQuasiCompact_of_isPullback B S hS sq hf
  -- Its fibre over the chart point is quasi-compact, hence covered by one affine étale chart.
  have hTcompact : IsCompact (setFibre B S hS (pullback.snd f b) pv) :=
    isCompact_setFibre_of_isQuasiCompact B S hS hW (isAlgebraicSpace_yoneda B S hS V₀)
      (pullback.snd f b) hpr₂qc pv
  obtain ⟨Z, c, hZaff, hcE, hcover⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS (pullback f b) hW hTcompact
  -- The commuting square of étale charts it induces.
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hgE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.fst f b) :=
    MorphismProperty.comp_mem _ _ _ hcE hpr₁E
  let k₀ : Z ⟶ V₀ := yoneda.preimage (c ≫ pullback.snd f b)
  have hk₀ : yoneda.map k₀ = c ≫ pullback.snd f b := yoneda.map_preimage _
  have hsq : (c ≫ pullback.fst f b) ≫ f = yoneda.map k₀ ≫ b := by
    rw [hk₀, Category.assoc, Category.assoc, sq.w]
  -- Every point of the fibre is hit by a point of the chart lying over the chart point.
  have hsharp : ∀ x : points B S hS X, pointsMap B S hS X f x = y →
      ∃ x' : points B S hS (yoneda.obj Z),
        pointsMap B S hS (yoneda.obj Z) (c ≫ pullback.fst f b) x' = x ∧
        pointsMap B S hS (yoneda.obj Z) (yoneda.map k₀) x' = v := by
    intro x hx
    obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS sq x v (hx.trans hv.symm)
    obtain ⟨z, hz⟩ := hcover (show w ∈ setFibre B S hS (pullback.snd f b) pv from
      hw₂.trans hpvc.symm)
    exact ⟨z, by rw [pointsMap_comp_apply, hz, hw₁], by rw [hk₀, pointsMap_comp_apply, hz, hw₂]⟩
  exact ⟨⟨CostructuredArrow.mk (c ≫ pullback.fst f b), hgE⟩, ⟨CostructuredArrow.mk b, hbE⟩,
    k₀, v, hZaff, hV₀aff, hsq, hv,
    fun x hx => ((hsharp x hx).imp fun _ h => h.1), hsharp⟩

/-- **The case of schemes of Tag 0CVZ, read inside the big fppf site.** Let `h : D ⟶ E` be a
morphism of the big fppf site of `S` whose morphism of schemes is of finite presentation, let
`G` be a quasi-coherent `𝒪_D`-module of finite presentation and let `ε` be a point of `E` such
that `G` is flat over `E` at every point of the fibre `h^{-1}(ε)`. Then there are étale
morphisms `p : D' ⟶ D` and `q : E' ⟶ E` of the site with `D'` and `E'` affine, a morphism
`k : D' ⟶ E'` over `h`, a point of `E'` over `ε` and the fibre `h^{-1}(ε)` inside the image of
`p`, such that `Γ(D', p^*G)` is projective over `Γ(E', 𝒪_{E'})`.

This is Tag 05KW,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre`, carried
into the site: the elementary étale neighbourhood and the étale cover of the fibre it produces
are affine, hence compact, so by Stacks 04T7
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`) the étale — in particular locally
of finite type — morphisms out of them do not raise the cardinal size past the site's cutoff,
and both are objects of the site. Affineness of `D` and of `E` is not needed. -/
theorem exists_isAffine_etale_hom_projective_sections_along_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D E : BigFppfOver B S hS) (h : D ⟶ E)
    (G : ((BigFppfOver.toScheme B S hS).obj D).Modules)
    (ε : (BigFppfOver.toScheme B S hS).obj E)
    (hfp : FinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hqc : G.IsQuasicoherent) (hGfp : G.IsFinitePresentation)
    (hflat : ∀ δ : (BigFppfOver.toScheme B S hS).obj D,
      (BigFppfOver.toScheme B S hS).map h δ = ε →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom) G δ) :
    ∃ (D' E' : BigFppfOver B S hS) (p : D' ⟶ D) (q : E' ⟶ E) (k : D' ⟶ E')
      (ε' : (BigFppfOver.toScheme B S hS).obj E'),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      k ≫ q = p ≫ h ∧
      (BigFppfOver.toScheme B S hS).map q ε' = ε ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj D') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E') ∧
      (BigFppfOver.toScheme B S hS).map h ⁻¹' {ε} ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map p) ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj G
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) := by
  have := hqc
  have := hGfp
  obtain ⟨N, Z, m, g, -, hNaff, hZaff, hgE, hcomm, hcov, hproj⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre
      ((BigFppfOver.toScheme B S hS).map h) G ε hfp fun x =>
        hflat _ (by
          have hx : ((BigFppfOver.toScheme B S hS).map h).fiberι ε x ∈
              (BigFppfOver.toScheme B S hS).map h ⁻¹' {ε} := by
            rw [← Scheme.Hom.range_fiberι]
            exact Set.mem_range_self x
          exact hx)
  have := hNaff
  have := hZaff
  have := hgE
  have hZsize : B.Contains Z :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt D.left.property
  have hNsize : B.Contains N.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType N.toBase).trans_lt E.left.property
  have hbaseD : (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map E.hom =
      B.inclusion.map D.hom :=
    congrArg (fun w => B.inclusion.map w) (Over.w h)
  let D' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (g ≫ B.inclusion.map D.hom) :
      B.obj hZsize ⟶ B.obj hS))
  let E' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk (N.toBase ≫ B.inclusion.map E.hom) :
      B.obj hNsize ⟶ B.obj hS))
  have hk : (ObjectProperty.homMk m : B.obj hZsize ⟶ B.obj hNsize) ≫ E'.hom = D'.hom := by
    refine ObjectProperty.hom_ext _ ?_
    show m ≫ N.toBase ≫ B.inclusion.map E.hom = g ≫ B.inclusion.map D.hom
    rw [← Category.assoc, ← hcomm, Category.assoc, hbaseD]
  refine ⟨D', E',
      Over.homMk (ObjectProperty.homMk g : B.obj hZsize ⟶ D.left) rfl,
      Over.homMk (ObjectProperty.homMk N.toBase : B.obj hNsize ⟶ E.left) rfl,
      Over.homMk (ObjectProperty.homMk m : B.obj hZsize ⟶ B.obj hNsize) hk, N.point,
      hgE, N.etale_toBase, ?_, N.map_point, hZaff, hNaff, hcov, hproj⟩
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  show m ≫ N.toBase = g ≫ (BigFppfOver.toScheme B S hS).map h
  exact hcomm.symm

/-- A scheme point `δ` of `U` mapping to the scheme point of `w` under `h : U ⟶ V` corresponds to
a point of `yoneda.obj U` mapping to `w`. -/
private theorem pointsMap_yoneda_symm_eq_of_map_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
    (h : U ⟶ V) (δ : (BigFppfOver.toScheme B S hS).obj U) (w : points B S hS (yoneda.obj V))
    (hδ : (BigFppfOver.toScheme B S hS).map h δ = pointsToScheme B S hS V w) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map h) ((pointsEquivScheme B S hS U).symm δ) = w := by
  refine injective_pointsToScheme B S hS V ?_
  rw [pointsToScheme_pointsMap_yoneda]
  exact (congrArg _ ((pointsEquivScheme B S hS U).apply_symm_apply δ)).trans hδ

/-- **Stacks Project, Tag 0CVZ.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
let `𝓕` be an `𝒪_X`-module and let `y` be a point of `|Y|`. Assume

1. `f` is of finite presentation (`hfp`, Stacks 03XP part (3));
2. `𝓕` is quasi-coherent and of finite presentation (`hqc`, `h𝓕fp`), chartwise: its restriction
   to every étale scheme chart of `X` is;
3. `𝓕` is flat over `Y` at every point of the fibre `F = f^{-1}({y})` (`hflat`), chartwise: on
   every commuting square of étale charts and at every point of the source chart lying over a
   point of `F`, the restriction of `𝓕` to the source chart is flat over the target chart there.

Then there are an étale chart `Z` of `X`, an étale chart `V` of `Y`, affine objects `X'`, `Y'`
of the site with étale morphisms `p : X' ⟶ Z` and `q : Y' ⟶ V`, a morphism `k : X' ⟶ Y'` and a
point `y'` of `|Y'|` such that the composites `X' → X` and `Y' → Y` are étale, the square
commutes over `f`, `y'` lies over `y`, the fibre `F` is contained in the image of `|X'| → |X|`,
and the sections `Γ(X', p^*(𝓕|_Z))` form a projective `Γ(Y', 𝒪_{Y'})`-module.

The conclusion is the conclusion of Tag 0CVZ, with no clause dropped, and nothing is granted as
a hypothesis: everything except the projectivity is
`AlgebraicGeometry.Space.exists_isAffine_etale_chart_square_along_fibre`, and the projectivity
is the case of schemes, Tag 05KW, read inside the site by
`AlgebraicGeometry.Space.exists_isAffine_etale_hom_projective_sections_along_fibre`.

Quasi-coherence and the hypotheses (2) and (3) are stated chartwise here; compare
`AlgebraicGeometry.Space.IsFlatOver`, the definition of Stacks 05VV. This is **not** the
source's reading of them, and it is not comparable to it: chartwise quasi-coherence and
chartwise finite presentation are weaker than the source's conditions on `X` itself, while the
chartwise flatness asked here is the every-chart-square form, which is strictly more than
Stacks 05VV asks at a point. The statement at the source's own three hypotheses, with no
chartwise condition on the module anywhere, is
`exists_isAffine_etale_charts_projective_sections_along_fibre_of_isFlatOverAtPoint`, which is
proved from this one. See the module docstring for the three transfers between the readings. -/
@[stacks 0CVZ "the full conclusion — the affine étale diagram covering the fibre and the \
projectivity of the sections — with quasi-coherence and the tag's conditions (2) and (3) on \
the module in their étale-chartwise form, for a consumer holding chart data; the case of \
schemes, Tag 05KW, is discharged inside the big fppf site"]
theorem exists_isAffine_etale_charts_projective_sections_along_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (𝓕 : Modules.{u, u} B S hS X hX) (y : points B S hS Y)
    (hfp : IsFinitePresentation B S hS f)
    (hqc : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX 𝓕 U).IsQuasicoherent)
    (h𝓕fp : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX 𝓕 U).IsFinitePresentation)
    (hflat : ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (x' : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))),
      U.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom →
      pointsMap B S hS X f (pointsMap B S hS _ U.obj.hom x') = y →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom)
        (restrictToChart B S hS hX 𝓕 U) (pointsToScheme B S hS _ x')) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (X' Y' : BigFppfOver B S hS)
      (p : X' ⟶ (SmallEtale.toOver B S hS X).obj U)
      (q : Y' ⟶ (SmallEtale.toOver B S hS Y).obj V) (k : X' ⟶ Y')
      (y' : points B S hS (yoneda.obj Y')),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p ≫ U.obj.hom) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ V.obj.hom) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj X') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y') ∧
      (yoneda.map p ≫ U.obj.hom) ≫ f = yoneda.map k ≫ yoneda.map q ≫ V.obj.hom ∧
      pointsMap B S hS _ (yoneda.map q ≫ V.obj.hom) y' = y ∧
      {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
        Set.range (pointsMap B S hS _ (yoneda.map p ≫ U.obj.hom)) ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj
           (restrictToChart B S hS hX 𝓕 U)
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤) Γ(M, ⊤)) := by
  classical
  -- The unconditional diagram.
  obtain ⟨U, V, k₀, y₀, hUaff, hVaff, hsq, hy₀, -, hsharp⟩ :=
    exists_isAffine_etale_chart_square_along_fibre B S hS hX hY f hfp.2.1 y
  have hUaff' : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X).obj U)) := hUaff
  have hVaff' : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y).obj V)) := hVaff
  -- Both charts being affine, the morphism of schemes is of finite presentation.
  have hk₀lfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k₀) :=
    hfp.1 _ _ U.obj.hom V.obj.hom k₀ U.property V.property hsq.symm
  have hk₀fp : FinitePresentation ((BigFppfOver.toScheme B S hS).map k₀) :=
    ⟨hk₀lfp, (quasiCompact_iff_compactSpace _).mpr inferInstance, inferInstance⟩
  set vs := pointsToScheme B S hS ((SmallEtale.toOver B S hS Y).obj V) y₀ with hvs
  -- Flatness holds along the whole fibre of that morphism of schemes.
  have hflatk : ∀ δ : (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj U),
      (BigFppfOver.toScheme B S hS).map k₀ δ = vs →
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map k₀).toLRSHom)
        (restrictToChart B S hS hX 𝓕 U) δ := by
    intro δ hδ
    have hback : pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj U)
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj U)).symm δ) = δ :=
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj U)).apply_symm_apply δ
    have hmapk : pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) (yoneda.map k₀)
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj U)).symm δ) = y₀ := by
      exact pointsMap_yoneda_symm_eq_of_map_eq B S hS k₀ δ y₀ hδ
    have hover : pointsMap B S hS X f (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) U.obj.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj U)).symm δ)) = y := by
      rwa [← pointsMap_comp_apply, hsq, pointsMap_comp_apply, hmapk]
    have hres := hflat U V k₀
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj U)).symm δ) hsq hover
    rwa [hback] at hres
  -- The case of schemes.
  obtain ⟨D', E', p, q, k, ε', hpE, hqE, hcomm, hqε, hD'aff, hE'aff, hcov, hproj⟩ :=
    exists_isAffine_etale_hom_projective_sections_along_fibre B S hS _ _ k₀
      (restrictToChart B S hS hX 𝓕 U) vs hk₀fp (hqc U) (h𝓕fp U) hflatk
  -- The resulting diagram is the one asked for.
  have hpEp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p ≫ U.obj.hom) :=
    etale_comp_of_scheme B S hS p U.obj.hom hpE U.property
  have hqEq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ V.obj.hom) :=
    etale_comp_of_scheme B S hS q V.obj.hom hqE V.property
  have hsqfin : (yoneda.map p ≫ U.obj.hom) ≫ f =
      yoneda.map k ≫ yoneda.map q ≫ V.obj.hom := by
    rw [Category.assoc, hsq, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hcomm]
  have hε'map : pointsMap B S hS (yoneda.obj E') (yoneda.map q)
      ((pointsEquivScheme B S hS E').symm ε') = y₀ := by
    exact pointsMap_yoneda_symm_eq_of_map_eq B S hS q ε' y₀ hqε
  have hy' : pointsMap B S hS (yoneda.obj E') (yoneda.map q ≫ V.obj.hom)
      ((pointsEquivScheme B S hS E').symm ε') = y := by
    rwa [pointsMap_comp_apply, hε'map]
  have hfibre : {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
      Set.range (pointsMap B S hS (yoneda.obj D') (yoneda.map p ≫ U.obj.hom)) := by
    intro x hx
    obtain ⟨x', hx'₁, hx'₂⟩ := hsharp x hx
    have hzk : (BigFppfOver.toScheme B S hS).map k₀
        (pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj U) x') = vs := by
      rw [← pointsToScheme_pointsMap_yoneda, hx'₂, hvs]
    obtain ⟨d, hd⟩ := hcov hzk
    have hdp : pointsMap B S hS (yoneda.obj D') (yoneda.map p)
        ((pointsEquivScheme B S hS D').symm d) = x' := by
      exact pointsMap_yoneda_symm_eq_of_map_eq B S hS p d x' hd
    exact ⟨(pointsEquivScheme B S hS D').symm d, by rwa [pointsMap_comp_apply, hdp]⟩
  exact ⟨U, V, D', E', p, q, k, (pointsEquivScheme B S hS E').symm ε',
    hpEp, hqEq, hD'aff, hE'aff, hsqfin, hy', hfibre, hproj⟩

/-- **Flatness over the target at a point of an algebraic space does not depend on the chart.**
If a quasi-coherent `𝒪_X`-module is flat over `Y` at a point `x` of `|X|` in the some-chart
sense of Stacks 05VV — on *some* commuting square of étale scheme charts and at *some* point of
the source chart above `x` — then it is flat over `Y` on *every* commuting square of étale
scheme charts, at *every* point of the source chart above `x`.

This is Stacks 05VU, through
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`: both the some-chart
condition and the asserted one are membership of `x` in the relative flat locus of
Stacks 0DLR, which names no chart. Quasi-coherence is the hypothesis of Stacks 05VP, which
that equivalence rests on, and is the hypothesis Tag 0CVZ makes on `𝓕`. -/
theorem isFlatOverAtOnChartDiagram_of_isFlatOverAtPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (𝓕 : Modules.{u, u} B S hS X hX) (h𝓕 : 𝓕.IsQuasicoherentOnSite)
    {x : points B S hS X} (hx : IsFlatOverAtPoint B S hS hX f 𝓕 x)
    (d : ChartDiagram B S hS X Y f) (u : etaleChartScheme B S hS d.U)
    (hu : pointOfEtaleChart B S hS d.U u = x) :
    IsFlatOverAtOnChartDiagram B S hS hX 𝓕 d u :=
  have := h𝓕
  (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS
      (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (ObjectProperty.homMk f) 𝓕 d u).2 (hu ▸ hx)

/-- **Stacks Project, Tag 0CVZ.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
let `𝓕` be a quasi-coherent `𝒪_X`-module and let `y` be a point of `|Y|` with fibre
`F = f^{-1}({y}) ⊆ |X|`. Assume

1. `f` is of finite presentation (`hfp`, Stacks 03XP part (3));
2. `𝓕` is of finite presentation (`h𝓕fp`), on the small étale site of `X`, which is the
   property Stacks 05VR item (l) names;
3. `𝓕` is flat over `Y` at every point of `F` (`hflat`), in the some-chart sense of
   Stacks 05VV, which is condition (1) of Stacks 05VU.

Then there are an étale chart `Z` of `X`, an étale chart `V` of `Y`, affine objects `X'`, `Y'`
of the site with étale morphisms `p : X' ⟶ Z` and `q : Y' ⟶ V`, a morphism `k : X' ⟶ Y'` and a
point `y'` of `|Y'|` such that the composites `X' → X` and `Y' → Y` are étale, the square
commutes over `f`, `y'` lies over `y`, the fibre `F` is contained in the image of `|X'| → |X|`,
and the sections `Γ(X', p^*(𝓕|_Z))` form a projective `Γ(Y', 𝒪_{Y'})`-module.

**Every hypothesis here is the source's own, and no chartwise condition on the module appears.**
This is `AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_along_fibre`
with its three chartwise hypotheses on the module discharged: quasi-coherence on the small étale
site gives chartwise quasi-coherence by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, finite presentation on the small
étale site gives chartwise finite presentation by
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`, and the
some-chart form of condition (3) gives the every-chart form by Stacks 05VU,
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_of_isFlatOverAtPoint`. -/
@[stacks 0CVZ "the full conclusion — the affine étale diagram covering the fibre and the \
projectivity of the sections — at the tag's own three conditions throughout: the module \
quasi-coherent and of finite presentation on the small étale site, and condition (3) in the \
some-chart form which Stacks 05VV gives it; no chartwise condition on the module appears, and \
the case of schemes, Tag 05KW, is discharged inside the big fppf site"]
theorem exists_isAffine_etale_charts_projective_sections_along_fibre_of_isFlatOverAtPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (𝓕 : Modules.{u, u} B S hS X hX) (y : points B S hS Y)
    (hfp : IsFinitePresentation B S hS f)
    (hqc : 𝓕.IsQuasicoherentOnSite)
    (h𝓕fp : SheafOfModules.IsFinitePresentationOnSite 𝓕)
    (hflat : ∀ x : points B S hS X, pointsMap B S hS X f x = y →
      IsFlatOverAtPoint B S hS hX f 𝓕 x) :
    ∃ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (X' Y' : BigFppfOver B S hS)
      (p : X' ⟶ (SmallEtale.toOver B S hS X).obj U)
      (q : Y' ⟶ (SmallEtale.toOver B S hS Y).obj V) (k : X' ⟶ Y')
      (y' : points B S hS (yoneda.obj Y')),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p ≫ U.obj.hom) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ V.obj.hom) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj X') ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y') ∧
      (yoneda.map p ≫ U.obj.hom) ≫ f = yoneda.map k ≫ yoneda.map q ≫ V.obj.hom ∧
      pointsMap B S hS _ (yoneda.map q ≫ V.obj.hom) y' = y ∧
      {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
        Set.range (pointsMap B S hS _ (yoneda.map p ≫ U.obj.hom)) ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map p)).obj
           (restrictToChart B S hS hX 𝓕 U)
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤) Γ(M, ⊤)) := by
  refine exists_isAffine_etale_charts_projective_sections_along_fibre B S hS hX hY f 𝓕 y hfp
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS ⟨X, hX⟩ 𝓕 hqc)
    (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS ⟨X, hX⟩ 𝓕 hqc h𝓕fp)
    fun U V g x' hsq hover => ?_
  have hpt : pointOfEtaleChart B S hS U (pointsToScheme B S hS _ x') =
      pointsMap B S hS _ U.obj.hom x' := by
    rw [pointOfEtaleChart]
    exact congrArg _ (injective_pointsToScheme B S hS U.obj.left
      ((pointsEquivScheme B S hS U.obj.left).apply_symm_apply _))
  exact isFlatOverAtOnChartDiagram_of_isFlatOverAtPoint B S hS hX hY f 𝓕 hqc
    (hflat _ hover) ⟨U, V, g, hsq⟩ (pointsToScheme B S hS _ x') hpt

end AlgebraicGeometry.Space

end
