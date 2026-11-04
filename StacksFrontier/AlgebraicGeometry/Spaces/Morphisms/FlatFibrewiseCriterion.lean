module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FibrewiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Critère de platitude par fibres for a morphism of algebraic spaces

Let `S` be a scheme and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over
`S` with `X`, `Y`, `Z` locally Noetherian, with `X` flat over `Z`, and with the fibre of `X`
over a point of `Z` flat over the fibre of `Y` over that point. Then `f` is flat, and if `f` is
moreover surjective then `Y` is flat over `Z`.

Flatness of a morphism of algebraic spaces is the every-étale-chart condition of Stacks 03MJ
for flatness of morphisms of schemes, so both conclusions are reached on one commuting pair of
chart squares. Building that pair is the whole geometric content of the reduction: a surjective
étale scheme atlas `c : h_W ⟶ Z` of `Z` is lifted through `g` to a surjective étale chart
`b : h_V ⟶ Y` presented over `W` by `k : V ⟶ W`, and then through `f` to a surjective étale
chart `a : h_U ⟶ X` presented over `V` by `h : U ⟶ V`. The three chart schemes are locally
Noetherian, the composite `U ⟶ W` is flat because `X` is flat over `Z`, and the fibrewise
hypothesis says exactly that each `U_w ⟶ V_w` is flat; the fibrewise criterion for schemes,
Stacks 039D, then gives flatness of `U ⟶ V`, and flatness of `V ⟶ W` as soon as `U ⟶ V` is
surjective. Since flatness of morphisms of schemes is étale local on the source and target,
one such surjective chart square suffices, which is Stacks 03MJ again.

## Main definitions

* `AlgebraicGeometry.Space.HasFlatFibreCharts` is the fibrewise flatness hypothesis of
  Stacks 0APS, read on étale charts: for every commuting pair of chart squares of `f` over `g`
  and every point `w` of the chart of `Z`, the induced morphism from the fibre of the chart of
  `X` at `w` to the fibre of the chart of `Y` at `w` is flat.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_flatFibreCharts`: **Stacks 0APS**, conclusion (A), `f` is
  flat.
* `AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_of_isSurjective`: **Stacks 0APS**,
  conclusion (B), `Y` is flat over `Z` when `f` is in addition surjective.

## What of Stacks 0APS is and is not proved

Both conclusions of the source are proved, with no carried hypotheses and no appeal to any
unproved statement: conclusion (A), flatness of `f`, is
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts`, and conclusion (B), flatness of `Y` over
`Z` for surjective `f`, is
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_of_isSurjective`.

Hypotheses (1) and (2) of the source are taken in their standard library spellings: local
Noetherianity of an algebraic space is `AlgebraicGeometry.Space.HasEtaleLocalProperty` of
Tag 03E6 for `AlgebraicGeometry.IsLocallyNoetherian`, as in
`AlgebraicGeometry.Space.IsNoetherian`, and flatness of `X` over `Z` is
`AlgebraicGeometry.Space.IsFlat` of the composite, part (1) of Tag 03ML.

Hypothesis (3) of the source — for every `z` in `|Z|` the fibre `X_z` is flat over the fibre
`Y_z` — is *not* taken in the form of a condition on the fibres of the spaces themselves. It is
taken in its every-étale-chart reading `AlgebraicGeometry.Space.HasFlatFibreCharts`, described
below; the equivalence of the two readings is not proved here, and no statement of this file
asserts it.

## Implementation notes

The chart reading of hypothesis (3) is the one the proof consumes, and it is a reading of the
hypothesis rather than a weakening of the theorem: for étale charts `a`, `b`, `c` of `X`, `Y`,
`Z` sitting over `h : U ⟶ V` and `k : V ⟶ W`, and `w` a point of the chart `W` above `z` in
`|Z|`, the morphism `U_w ⟶ V_w` is the base change of `X_z ⟶ Y_z` to the residue field of `w`
read through the étale morphisms `U_w ⟶ X_z ⊗ κ(w)` and `V_w ⟶ Y_z ⊗ κ(w)`, so it is flat
exactly when `X_z ⟶ Y_z` is, flatness of schemes being stable under base change and étale
local on the source and target. That comparison of a fibre of an algebraic space with the
scheme-theoretic fibre of a chart is available in this library only for *object* properties —
`AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff` — and not for a property of a
morphism *between* two such fibres, which is why the chart reading is what is stated. The
precedent is `AlgebraicGeometry.Space.HasLocallyNoetherianFibers`, the every-chart reading of
the standing fibre hypothesis of Tag 0E0W.

The chart squares come from `AlgebraicGeometry.Space.exists_etale_chart_square_over`, whose
last conclusion is what makes conclusion (B) available: the morphism of schemes it produces is
surjective as soon as the morphism of algebraic spaces is surjective on points, which is the
input that `AlgebraicGeometry.flat_of_flat_fiberHom_of_surjective` needs and which
surjectivity of the two charts alone would not supply. Local Noetherianity of the three chart
schemes is read off the some-chart condition by
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` (Tag 03E8), which applies to an
arbitrary étale chart and not only to a surjective one; this is why the charts need not be
refined. Passage from one surjective chart square to all chart
squares is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart` together with
`AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget` (Tag 04R3).

Flatness of the chart of `X` over the chart of `Z` is obtained by feeding the composite
`h ≫ k` to the hypothesis that `X` is flat over `Z`; the two chart squares compose to the one
square this needs, which is the only place the hypothesis on the composite is used.

## References

* [Stacks Project, Tag 0APS](https://stacks.math.columbia.edu/tag/0APS)
* [Stacks Project, Tag 039D](https://stacks.math.columbia.edu/tag/039D)
* [Stacks Project, Tag 039E](https://stacks.math.columbia.edu/tag/039E)
* [Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0E0W](https://stacks.math.columbia.edu/tag/0E0W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The fibrewise flatness hypothesis of Stacks 0APS, read on étale charts.** For
`f : X ⟶ Y` and `g : Y ⟶ Z` morphisms of algebraic spaces over `S`, this says that for every
commuting pair of étale chart squares — charts `a`, `b`, `c` of `X`, `Y`, `Z` presented over
morphisms `h : U ⟶ V` and `k : V ⟶ W` of the site — and every point `w` of the chart scheme of
`Z`, the canonical morphism from the fibre of `U ⟶ W` at `w` to the fibre of `V ⟶ W` at `w` is
flat.

This is the every-chart reading of hypothesis (3) of the source, that the fibre of `X` over a
point of `|Z|` be flat over the fibre of `Y` over that point. -/
abbrev HasFlatFibreCharts (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∀ (U V W : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (c : yoneda.obj W ⟶ Z) (h : U ⟶ V) (k : V ⟶ W),
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c →
    yoneda.map h ≫ b = a ≫ f →
    yoneda.map k ≫ c = b ≫ g →
    ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      _root_.AlgebraicGeometry.Flat (Stacks.Flatness.fiberHom
        ((BigFppfOver.toScheme B S hS).map h) ((BigFppfOver.toScheme B S hS).map k) w)

/-- **The surjective chart square carrying both conclusions of Stacks 0APS.** Under the three
hypotheses of the source, flatness of morphisms of schemes holds on one surjective étale chart
square of `f`, and — as soon as `f` is surjective on points — on one surjective étale chart
square of `g`.

Both are read off the same pair of chart squares, so they are produced together: the fibrewise
criterion for schemes, Stacks 039D, delivers flatness of the chart morphism of `f` and, when
that chart morphism is surjective, flatness of the chart morphism of `g`. -/
private theorem holdsOnSurjectiveEtaleChart_flat_pair
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXn : HasEtaleLocalProperty B S hS X
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hYn : HasEtaleLocalProperty B S hS Y
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hZn : HasEtaleLocalProperty B S hS Z
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hflat : IsFlat B S hS (f ≫ g)) (hfib : HasFlatFibreCharts B S hS f g) :
    HoldsOnSurjectiveEtaleChart B S hS
        (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) f ∧
      (IsSurjective B S hS f → HoldsOnSurjectiveEtaleChart B S hS
        (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) g) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨W, c, hcS, hcE⟩ := hZ.exists_atlas
  obtain ⟨V, b, k, hbE, hkcomm, hbSof, -⟩ :=
    exists_etale_chart_square_over B S hS hY hZ g W c hcE
  obtain ⟨U, a, h, haE, hhcomm, haSof, hhSof⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hbE
  have hbS := hbSof hcS
  -- The three chart schemes are locally Noetherian.
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (T.obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp hXn U a haE
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (T.obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y _ hY).mp hYn V b hbE
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (T.obj W) :=
    (exists_atlas_iff_forall_etale B S hS Z _ hZ).mp hZn W c hcE
  -- The chart of `X` is flat over the chart of `Z`, the two squares composing to one square.
  have : _root_.AlgebraicGeometry.Flat (T.map h ≫ T.map k) := by
    rw [← Functor.map_comp]
    exact hflat U W a c (h ≫ k) haE hcE
      (by rw [Functor.map_comp, Category.assoc, hkcomm, reassoc_of% hhcomm])
  -- The fibrewise hypothesis at this pair of squares.
  have hfibchart : ∀ w : T.obj W, _root_.AlgebraicGeometry.Flat
      (Stacks.Flatness.fiberHom (T.map h) (T.map k) w) :=
    hfib U V W a b c h k haE hbE hcE hhcomm hkcomm
  refine ⟨⟨U, V, a, b, h, haE, hbE, haSof hbS, hhcomm,
    _root_.AlgebraicGeometry.flat_of_flat_fiberHom (T.map h) (T.map k) hfibchart⟩,
    fun hfs => ?_⟩
  have := hhSof hfs
  exact ⟨V, W, b, c, k, hbE, hcE, hbS, hkcomm,
    _root_.AlgebraicGeometry.flat_of_flat_fiberHom_of_surjective (T.map h) (T.map k) hfibchart⟩

/-- **Stacks Project, Tag 0APS, conclusion (A).** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms
of algebraic spaces over a scheme `S`. If `X`, `Y`, `Z` are locally Noetherian, `X` is flat
over `Z`, and the fibres of `X` over the points of `Z` are flat over the corresponding fibres
of `Y` in the chart sense of `AlgebraicGeometry.Space.HasFlatFibreCharts`, then `f` is
flat. -/
@[stacks 0APS "conclusion (A): flatness of the morphism; hypothesis (3) in its every-étale-chart
reading `AlgebraicGeometry.Space.HasFlatFibreCharts`"]
theorem isFlat_of_flatFibreCharts
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXn : HasEtaleLocalProperty B S hS X
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hYn : HasEtaleLocalProperty B S hS Y
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hZn : HasEtaleLocalProperty B S hS Z
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hflat : IsFlat B S hS (f ≫ g)) (hfib : HasFlatFibreCharts B S hS f g) :
    IsFlat B S hS f :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hX hY f).mpr
    (holdsOnSurjectiveEtaleChart_flat_pair B S hS hX hY hZ f g hXn hYn hZn hflat hfib).1

/-- **Stacks Project, Tag 0APS, conclusion (B).** In the situation of
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts`, if `f` is in addition surjective then `Y`
is flat over `Z`. -/
@[stacks 0APS "conclusion (B): flatness of the target over the base for surjective `f`;
hypothesis (3) in its every-étale-chart reading
`AlgebraicGeometry.Space.HasFlatFibreCharts`"]
theorem isFlat_of_flatFibreCharts_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXn : HasEtaleLocalProperty B S hS X
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hYn : HasEtaleLocalProperty B S hS Y
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hZn : HasEtaleLocalProperty B S hS Z
      (fun A : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian A))
    (hflat : IsFlat B S hS (f ≫ g)) (hfib : HasFlatFibreCharts B S hS f g)
    (hfs : IsSurjective B S hS f) :
    IsFlat B S hS g :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hY hZ g).mpr
    ((holdsOnSurjectiveEtaleChart_flat_pair B S hS hX hY hZ f g hXn hYn hZn hflat hfib).2 hfs)

end AlgebraicGeometry.Space

end
