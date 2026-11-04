module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatFibrewiseCriterion

/-!
# Critère de platitude par fibres for a morphism of algebraic spaces, finitely presented case

Let `S` be a scheme and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over
`S`. Assume

1. `X` is locally of finite presentation over `Z`,
2. `X` is flat over `Z`,
3. for every `z ∈ |Z|` the fibre of `X` over `z` is flat over the fibre of `Y` over `z`, and
4. `Y` is locally of finite type over `Z`.

Then `f` is flat, and if `f` is moreover surjective then `Y` is flat over `Z`.

This is the finite-presentation form of
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts`, which assumes instead that the three
spaces are locally Noetherian. Flatness of a morphism of algebraic spaces is the
every-étale-chart condition of Stacks 03MJ for flatness of morphisms of schemes, so both
conclusions are reached on one commuting pair of chart squares: a surjective étale scheme
atlas `c : h_W ⟶ Z` of `Z` is lifted through `g` to a surjective étale chart `b : h_V ⟶ Y`
presented over `W` by `k : V ⟶ W`, and then through `f` to a surjective étale chart
`a : h_U ⟶ X` presented over `V` by `h : U ⟶ V`. The composite `U ⟶ W` is flat and locally of
finite presentation because `X` is flat and locally of finite presentation over `Z`, the
morphism `V ⟶ W` is locally of finite type because `Y` is locally of finite type over `Z`, and
the fibrewise hypothesis says exactly that each `U_w ⟶ V_w` is flat; the fibrewise criterion
for schemes, Stacks 039E, then gives flatness of `U ⟶ V`, and flatness of `V ⟶ W` as soon as
`U ⟶ V` is surjective. Since flatness of morphisms of schemes is étale local on the source and
target, one such surjective chart square suffices, which is Stacks 03MJ again.

## Main definitions

There are no new definitions. The fibrewise flatness hypothesis is
`AlgebraicGeometry.Space.HasFlatFibreCharts`, the every-étale-chart reading of hypothesis (3)
introduced in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FlatFibrewiseCriterion.lean`.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_finitePresentation`: **Stacks 05X1**, the
  first conclusion, `f` is flat.
* `AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_finitePresentation_of_isSurjective`:
  **Stacks 05X1**, the second conclusion, `Y` is flat over `Z` when `f` is in addition
  surjective.

## What of Stacks 05X1 is and is not proved

Both conclusions of the source are proved, with no appeal to any unproved statement, and no
hypothesis of the source is dropped: the first conclusion, flatness of `f`, is
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_finitePresentation`, and the second,
flatness of `Y` over `Z` for surjective `f`, is
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_finitePresentation_of_isSurjective`.

Hypotheses (1), (2) and (4) of the source are taken in their standard library spellings: local
finite presentation of `X` over `Z` is `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`
of the composite, part (1) of Tag 03XP; flatness of `X` over `Z` is
`AlgebraicGeometry.Space.IsFlat` of the composite, part (1) of Tag 03ML; and local finite type
of `Y` over `Z` is `AlgebraicGeometry.Space.IsLocallyOfFiniteType`, part (1) of Tag 03XF.
Surjectivity of `f` is `AlgebraicGeometry.Space.IsSurjective` of Tag 03ME.

Hypothesis (3) of the source — for every `z` in `|Z|` the fibre `X_z` is flat over the fibre
`Y_z` — is **carried in its every-étale-chart reading**
`AlgebraicGeometry.Space.HasFlatFibreCharts`, exactly as in the locally Noetherian form
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts` of Tag 0APS. The equivalence of that
reading with a condition on the fibres of the spaces themselves is not proved here, and no
statement of this file asserts it; the comparison of a fibre of an algebraic space with the
scheme-theoretic fibre of a chart is available in this library only for *object* properties,
`AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff`, and not for a property of a
morphism between two such fibres.

## Implementation notes

The chart reading of hypothesis (3) is the one the proof consumes, and it is a reading of the
hypothesis rather than a weakening of the theorem: for étale charts `a`, `b`, `c` of `X`, `Y`,
`Z` sitting over `h : U ⟶ V` and `k : V ⟶ W`, and `w` a point of the chart `W` above `z` in
`|Z|`, the morphism `U_w ⟶ V_w` is the base change of `X_z ⟶ Y_z` to the residue field of `w`
read through the étale morphisms `U_w ⟶ X_z ⊗ κ(w)` and `V_w ⟶ Y_z ⊗ κ(w)`, so it is flat
exactly when `X_z ⟶ Y_z` is, flatness of schemes being stable under base change and étale
local on the source and target.

The source deduces this lemma from the module form of the criterion, Stacks 05X0, by taking the
module to be `𝒪_X`. The route taken here is the one the locally Noetherian form of the same
statement takes: the scheme-level criterion applies to the chart morphisms directly, so no
identification of the geometric stalk of the structure sheaf with the étale local ring is
needed, and the finiteness hypotheses are consumed where the source's own proof of Stacks 05X0
consumes them, namely on a composable pair of chart squares.

The chart squares come from `AlgebraicGeometry.Space.exists_etale_chart_square_over`, whose
last conclusion is what makes the second conclusion available: the morphism of schemes it
produces is surjective as soon as the morphism of algebraic spaces is surjective on points,
which is the input that `Stacks.Flatness.flat_of_flat_fiberHom_of_surjective` needs and which
surjectivity of the two charts alone would not supply. Passage from one surjective chart square
to all chart squares is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`
together with `AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget` (Tag 04R3).

Flatness and local finite presentation of the chart of `X` over the chart of `Z` are obtained
by feeding the composite `h ≫ k` to the hypotheses on the composite `f ≫ g`; the two chart
squares compose to the one square this needs, which is the only place those hypotheses are
used.

## References

* [Stacks Project, Tag 05X1](https://stacks.math.columbia.edu/tag/05X1)
* [Stacks Project, Tag 05X0](https://stacks.math.columbia.edu/tag/05X0)
* [Stacks Project, Tag 039E](https://stacks.math.columbia.edu/tag/039E)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0APS](https://stacks.math.columbia.edu/tag/0APS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The surjective chart square carrying both conclusions of Stacks 05X1.** Under the four
hypotheses of the source, flatness of morphisms of schemes holds on one surjective étale chart
square of `f`, and — as soon as `f` is surjective on points — on one surjective étale chart
square of `g`.

Both are read off the same pair of chart squares, so they are produced together: the fibrewise
criterion for schemes, Stacks 039E, delivers flatness of the chart morphism of `f` and, when
that chart morphism is surjective, flatness of the chart morphism of `g`. -/
private theorem holdsOnSurjectiveEtaleChart_flat_pair_finitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfp : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hflat : IsFlat B S hS (f ≫ g)) (hft : IsLocallyOfFiniteType B S hS g)
    (hfib : HasFlatFibreCharts B S hS f g) :
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
  -- The two chart squares compose to one square over the composite `f ≫ g`.
  have hsquare : yoneda.map (h ≫ k) ≫ c = a ≫ (f ≫ g) := by
    simp [hkcomm, reassoc_of% hhcomm]
  -- The chart of `X` is flat and locally of finite presentation over the chart of `Z`, and
  -- the chart of `Y` is locally of finite type over the chart of `Z`.
  have hcomp : _root_.AlgebraicGeometry.Flat (T.map h ≫ T.map k) :=
    hflat U W a c (h ≫ k) haE hcE hsquare
  have hcompfp : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      (T.map h ≫ T.map k) :=
    hfp U W a c (h ≫ k) haE hcE hsquare
  have hkft : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map k) :=
    hft V W b c k hbE hcE hkcomm
  -- The fibrewise hypothesis at this pair of squares.
  have hfibchart : ∀ w : T.obj W, _root_.AlgebraicGeometry.Flat
      (Stacks.Flatness.fiberHom (T.map h) (T.map k) w) :=
    hfib U V W a b c h k haE hbE hcE hhcomm hkcomm
  refine ⟨⟨U, V, a, b, h, haE, hbE, haSof hbS, hhcomm,
    Stacks.Flatness.flat_of_flat_fiberHom (T.map h) (T.map k) hfibchart⟩, fun hfs => ?_⟩
  have _ : _root_.AlgebraicGeometry.Surjective (T.map h) := hhSof hfs
  exact ⟨V, W, b, c, k, hbE, hcE, hbS, hkcomm,
    Stacks.Flatness.flat_of_flat_fiberHom_of_surjective (T.map h) (T.map k) hfibchart⟩

/-- **Stacks Project, Tag 05X1, the first conclusion.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over a scheme `S`. If `X` is locally of finite presentation over
`Z`, `X` is flat over `Z`, the fibres of `X` over the points of `Z` are flat over the
corresponding fibres of `Y` in the chart sense of
`AlgebraicGeometry.Space.HasFlatFibreCharts`, and `Y` is locally of finite type over `Z`, then
`f` is flat. -/
@[stacks 05X1 "the first conclusion: flatness of `f`. Hypotheses (1), (2) and (4) are the \
library spellings Space.IsLocallyOfFinitePresentation of `f ≫ g`, Space.IsFlat of `f ≫ g` and \
Space.IsLocallyOfFiniteType of `g`; hypothesis (3) is CARRIED in its every-etale-chart reading \
Space.HasFlatFibreCharts, as in the locally Noetherian form Space.isFlat_of_flatFibreCharts of \
Stacks 0APS, the comparison of a fibre of an algebraic space with the scheme-theoretic fibre \
of a chart being available in this library only for properties of objects \
(Space.hasEtaleLocalProperty_fiberAt_iff) and not for a property of a morphism between two \
such fibres."]
theorem isFlat_of_flatFibreCharts_finitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfp : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hflat : IsFlat B S hS (f ≫ g)) (hft : IsLocallyOfFiniteType B S hS g)
    (hfib : HasFlatFibreCharts B S hS f g) :
    IsFlat B S hS f :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hX hY f).mpr
    (holdsOnSurjectiveEtaleChart_flat_pair_finitePresentation
      B S hS hX hY hZ f g hfp hflat hft hfib).1

/-- **Stacks Project, Tag 05X1, the second conclusion.** In the situation of
`AlgebraicGeometry.Space.isFlat_of_flatFibreCharts_finitePresentation`, if `f` is in addition
surjective then `Y` is flat over `Z`. -/
@[stacks 05X1 "the second conclusion: flatness of `Y` over `Z` for surjective `f`, with \
surjectivity taken as Space.IsSurjective of Stacks 03ME. Hypotheses (1), (2) and (4) are the \
library spellings Space.IsLocallyOfFinitePresentation of `f ≫ g`, Space.IsFlat of `f ≫ g` and \
Space.IsLocallyOfFiniteType of `g`; hypothesis (3) is CARRIED in its every-etale-chart reading \
Space.HasFlatFibreCharts, as in the locally Noetherian form \
Space.isFlat_of_flatFibreCharts_of_isSurjective of Stacks 0APS, the comparison of a fibre of \
an algebraic space with the scheme-theoretic fibre of a chart being available in this library \
only for properties of objects and not for a property of a morphism between two such fibres."]
theorem isFlat_of_flatFibreCharts_finitePresentation_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfp : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hflat : IsFlat B S hS (f ≫ g)) (hft : IsLocallyOfFiniteType B S hS g)
    (hfib : HasFlatFibreCharts B S hS f g) (hfs : IsSurjective B S hS f) :
    IsFlat B S hS g :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hY hZ g).mpr
    ((holdsOnSurjectiveEtaleChart_flat_pair_finitePresentation
      B S hS hX hY hZ f g hfp hflat hft hfib).2 hfs)

end AlgebraicGeometry.Space

end
