module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatAtRelativeAssassinPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativeFlatnessGeneralization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FibrePointsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypeGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction

/-!
# Flatness at a point and at the relative associated points of its fibre

Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `𝓕` be a quasi-coherent `𝒪_X`-module of finite type, let `x` be a
point of `|X|` with image `y` in `|Y|` and let `F = f^{-1}({y}) ⊆ |X|` be the set-theoretic
fibre. Stacks 0CWL considers the two conditions

1. `𝓕` is flat at `x` over `Y`, and
2. for every `x' ∈ F ∩ Ass_{X/Y}(𝓕)` which specializes to `x`, `𝓕` is flat at `x'` over `Y`,

and asserts that (2) always implies (1), and that (1) implies (2) when `X` and `Y` are decent.
This file proves both implications, by the source's argument: both are the case of schemes read
on a commuting square of étale scheme charts of `f`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_of_forall_isRelativeWeaklyAssociatedPoint`:
  **Stacks 0CWL, the implication (2) ⟹ (1)**, unconditionally.
* `AlgebraicGeometry.Space.isFlatOverAtPoint_of_specializes_of_isDecentSpace`:
  **Stacks 0CWL, the implication (1) ⟹ (2) for decent `X`**, unconditionally, and in the
  stronger form that drops the relative-assassin condition on `x'`, the condition that `x'` lie
  in the fibre through `x`, and decency of `Y`.

## Implementation notes

Flatness of `𝓕` over `Y` at a point is `AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV
part (1) read at a point of `|X|` through condition (1) of Stacks 05VU; the set `Ass_{X/Y}(𝓕)`
is `AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint` of Stacks 0CV0, which is
`WeakAss_{X/Y}(𝓕)` and is the set the source writes `Ass_{X/Y}(𝓕)` exactly because the fibres
of a morphism locally of finite type are locally Noetherian, Stacks 0CUY. Membership of `x'` in
the set-theoretic fibre `F` is equality of the images of `x'` and `x` under `|f|`.

Both proofs choose, by `AlgebraicGeometry.Space.exists_chartDiagram_pointOfEtaleChart`, a
commuting square `d` of étale scheme charts of `f` and a point `u` of its source chart scheme
cutting `x` out, and then read everything on the vertical morphism of chart schemes
`q = ` `AlgebraicGeometry.Space.chartDiagramSchemeMap`:

* flatness over `Y` at a point of `|X|` is flatness of the chart restriction over the target
  chart at any one chart point cutting it out, in both directions, by
  `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram`, which is
  Stacks 05VU and asks only for quasi-coherence;
* `q` is locally of finite type by
  `AlgebraicGeometry.Space.locallyOfFiniteType_chartDiagramSchemeMap`, and the chart restriction
  of `𝓕` is quasi-coherent and of finite type by
  `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` and
  `AlgebraicGeometry.Space.isFiniteType_restrictToChart`;
* the square commutes on points, `AlgebraicGeometry.Space.pointOfEtaleChart_map_g`, so a chart
  point lying in the fibre of `q` over `q u` cuts out a point of `|X|` in the set-theoretic
  fibre over `y`, and conversely;
* the chart is continuous on points, `AlgebraicGeometry.Space.continuous_pointOfEtaleChart`, so
  specializations in the chart scheme map to specializations in `|X|`.

For the implication (2) ⟹ (1) the remaining ingredient is the relative assassin: a point of the
Zariski relative assassin `Ass_{U/V}` of Stacks 05AT of `q` cuts out a point of
`WeakAss_{X/Y}(𝓕)`, which is
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram`
and is unconditional. So the hypothesis (2) on the algebraic space supplies exactly the
hypothesis (2) of the case of schemes on `q`, and the case of schemes is
`AlgebraicGeometry.isFlatOverAt_of_forall_mem_relativeAssassin_specializes` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatAtRelativeAssassinPoints.lean`: More on Flatness
Theorem 05UA (2) ⟹ (1), with its clause (2) read on the relative assassin rather than on the
associated points of the scheme-theoretic fibre, the two being identified over `q p` by
`Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin`.

For the implication (1) ⟹ (2) the case of schemes is
`AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres` of
`StacksFrontier/AlgebraicGeometry/Flatness/RelativeFlatnessGeneralization.lean`, which propagates
relative flatness of a quasi-coherent module to an arbitrary generalization of a point, since
the stalk at the generalization is a localization of the stalk at the point while the stalk of
the base, if it moves at all, moves to a localization of itself. In particular it does *not*
ask the two points to lie in one fibre, so the only input needed here is

* decency of `X`, which lifts the specialization `x' ⤳ x` to a specialization `u' ⤳ u` of chart
  points with `u'` above `x'`: Stacks 03IL,
  `AlgebraicGeometry.Space.exists_specialization_lift_of_isDecentSpace`.

Decency of `Y` is **not** needed. The source's argument puts the two lifted points in one fibre
of the chart morphism `q` so as to apply the same-fibre form of the scheme case; that step uses
Stacks 03K5,
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`, and decency of `Y`
with it, because a fibre of an étale morphism of algebraic spaces can carry a nontrivial
specialization — as this library witnesses in
`Stacks.Examples.EtaleSpecialization.exists_isEtale_specializes_pointsMap_eq` of
`StacksFrontier/Examples/Spaces/EtaleSpecializationInFibre.lean`, tagged `@[stacks 06UK]`. With the
scheme case available at an arbitrary generalization the step is unnecessary.

What is proved for (1) ⟹ (2) is stronger than the tag's clause (2) in four ways, all harmless:
the conclusion is drawn at *every* point of `|X|` specializing to `x`, not only at those lying
in `Ass_{X/Y}(𝓕)`, and not only at those lying in the set-theoretic fibre through `x`; decency
of `Y` is not assumed; and neither local finiteness of the type of `f` nor finiteness of the
type of `𝓕` is needed, so neither is a hypothesis.

The source phrases the reduction through a surjective étale `V → Y` and a surjective étale
`U → V ×_Y X`, and identifies `Ass_{U/V}(𝓕|_U) ∩ |U_v|` with `Ass_{U_v}(𝓕|_{U_v})` and with the
inverse image of `F ∩ Ass_{X/Y}(𝓕)`. Here a single commuting square of étale scheme charts
through the point plays that role, which is what the chart-diagram API of this library provides,
and the identification of the two assassins is the chart-diagram comparison cited above rather
than a passage through the fibre.

## References

* [Stacks Project, Theorem 77.6.3 (Tag 0CWL)](https://stacks.math.columbia.edu/tag/0CWL)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] pointTopology

/-! ### Stacks 0CWL, the implication (2) ⟹ (1) -/

/-- **Stacks 0CWL, the implication (2) ⟹ (1).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type, let `𝓕` be a quasi-coherent `𝒪_X`-module of
finite type and let `x` be a point of `|X|` with image `y` under `|f|`. If `𝓕` is flat over `Y`
at every point `x'` of `|X|` which lies over `y`, lies in the relative weak assassin
`WeakAss_{X/Y}(𝓕)` of Stacks 0CV0 — which is `Ass_{X/Y}(𝓕)` here, the fibres of `f` being
locally Noetherian — and specializes to `x`, then `𝓕` is flat over `Y` at `x`.

No decency is required, as the source records. Nothing is carried: the case of schemes is
`AlgebraicGeometry.isFlatOverAt_of_forall_mem_relativeAssassin_specializes`, More on Flatness
Theorem 05UA (2) ⟹ (1) in relative-assassin form, and the reduction to a commuting square of
étale scheme charts of `f` is what is proved here. -/
@[stacks 0CWL "the implication (2) => (1), which the tag asserts holds with no decency \
hypothesis: for f locally of finite type and F a finite type quasi-coherent module, flatness \
of F over Y at every point of the fibre over y which lies in Ass_{X/Y}(F) and specializes to x \
gives flatness of F over Y at x. UNCONDITIONAL -- nothing is carried: the case of schemes is \
More on Flatness Theorem 05UA (2) => (1), proved in this library as \
AlgebraicGeometry.isFlatOverAt_of_forall_mem_relativeAssassin_specializes, and the reduction \
to a commuting square of etale scheme charts is proved here"]
theorem isFlatOverAtPoint_of_forall_isRelativeWeaklyAssociatedPoint (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (x : points B S hS X.1)
    (h2 : ∀ x' : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x' = pointsMap B S hS X.1 f.hom x →
      IsRelativeWeaklyAssociatedPoint B S hS f F x' → x' ⤳ x →
        IsFlatOverAtPoint B S hS X.2 f.hom F x') :
    IsFlatOverAtPoint B S hS X.2 f.hom F x := by
  obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 Y.2 f.hom x
  subst hu
  have hq : LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
    locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have hNqc : SheafOfModules.IsQuasicoherent (chartDiagramRestrictSource B S hS f F d) :=
    isQuasicoherent_restrictToChart B S hS X F hF d.U
  have hNft : SheafOfModules.IsFiniteType (chartDiagramRestrictSource B S hS f F d) :=
    isFiniteType_restrictToChart B S hS X F hF hFft d.U
  have key : IsFlatOverAt (chartDiagramSchemeMap B S hS f d).toLRSHom.toShHom
      (chartDiagramRestrictSource B S hS f F d) u := by
    refine isFlatOverAt_of_forall_mem_relativeAssassin_specializes
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) u ?_
    intro u' hbase hass hspec
    have hpt : IsFlatOverAtPoint B S hS X.2 f.hom F (pointOfEtaleChart B S hS d.U u') := by
      refine h2 _ ?_ ?_ ?_
      · rw [← pointOfEtaleChart_map_g, ← pointOfEtaleChart_map_g]
        exact congrArg (pointOfEtaleChart B S hS d.V) hbase
      · have hpe : pointOfEtaleChart B S hS d.U u' = chartSchemeToPoints B S hS X.1 d.U u' :=
          (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.U u').symm
        rw [hpe]
        exact isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram
          B S hS f F hF d u' hass
      · exact hspec.map (continuous_pointOfEtaleChart B S hS d.U)
    exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u').1 hpt
  exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u).2 key

/-! ### Stacks 0CWL, the implication (1) ⟹ (2) -/

/-- **Stacks 0CWL, the implication (1) ⟹ (2), for decent `X`.** Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` with `X` decent and let `𝓕` be a quasi-coherent `𝒪_X`-module which
is flat over `Y` at a point `x` of `|X|`. Then `𝓕` is flat over `Y` at every point `x'` of `|X|`
which specializes to `x`.

This is clause (2) of the tag and more, in four ways: the relative-assassin condition on `x'` is
not needed; `x'` is not required to lie in the set-theoretic fibre of `f` through `x`; decency
of `Y` is not needed; and neither local finiteness of the type of `f` nor finiteness of the type
of `𝓕` is a hypothesis. Decency of `X` lifts the specialization to an étale scheme chart
(Stacks 03IL), and the case of schemes is then
`AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres`, which propagates relative flatness
to an arbitrary generalization and so asks nothing about the images of the two lifted points in the
target chart scheme. -/
@[stacks 0CWL "the implication (1) => (2) for decent X, UNCONDITIONALLY -- nothing is carried: \
flatness of F over Y at x gives flatness of F over Y at every point of |X| which specializes \
to x. This is stronger than the tag's clause (2) in four ways: the point is not required to \
lie in Ass_{X/Y}(F), it is not required to lie in the set-theoretic fibre through x, decency \
of Y is not needed, and f locally of finite type and F of finite type are not needed and are \
not hypotheses; quasi-coherence of F and decency of X are"]
theorem isFlatOverAtPoint_of_specializes_of_isDecentSpace (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hXdec : IsDecentSpace B S hS X.1)
    {x x' : points B S hS X.1} (hflat : IsFlatOverAtPoint B S hS X.2 f.hom F x)
    (hspec : x' ⤳ x) :
    IsFlatOverAtPoint B S hS X.2 f.hom F x' := by
  obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 Y.2 f.hom x
  have hNqc : SheafOfModules.IsQuasicoherent (chartDiagramRestrictSource B S hS f F d) :=
    isQuasicoherent_restrictToChart B S hS X F hF d.U
  obtain ⟨p', hp'spec, hp'img⟩ := exists_specialization_lift_of_isDecentSpace B S hS X.1 X.2
    hXdec x x' hspec d.U.obj.left d.U.obj.hom d.U.property
    ((pointsEquivScheme B S hS d.U.obj.left).symm u) hu
  have hu'pt : pointOfEtaleChart B S hS d.U (schemePointsHomeomorph B S hS d.U.obj.left p') =
      x' := by
    rw [pointOfEtaleChart]
    exact (congrArg _ ((pointsEquivScheme B S hS d.U.obj.left).symm_apply_apply p')).trans hp'img
  have hu'spec : schemePointsHomeomorph B S hS d.U.obj.left p' ⤳ u := by
    rw [← (pointsEquivScheme B S hS d.U.obj.left).apply_symm_apply u]
    exact hp'spec.map (schemePointsHomeomorph B S hS d.U.obj.left).continuous
  rw [← hu'pt]
  exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d _).2
    (@isFlatOverAt_of_specializes_acrossFibres _ _ (chartDiagramSchemeMap B S hS f d)
      (chartDiagramRestrictSource B S hS f F d) hNqc u _ hu'spec
      ((isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u).1
        (by rw [hu]; exact hflat)))

end AlgebraicGeometry.Space

end
