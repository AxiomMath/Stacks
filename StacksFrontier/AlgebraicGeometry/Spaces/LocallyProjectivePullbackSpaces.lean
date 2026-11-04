module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyProjectiveEtaleChart

/-!
# Pullback of a locally projective module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `G` be a quasi-coherent `𝒪_Y`-module whose restriction to every étale scheme chart of `Y` is
locally projective in the sense of Stacks 05JP.  This file proves **Stacks 060S**: the inverse
image `f^*G` of Stacks 03LU restricts to a locally projective module on every étale scheme chart
of `X`.

The argument is the source's own.  Choose an étale chart `V` of `Y` surjective on points and
lift it through `f` to an étale chart `U₀` of `X` surjective on points together with a morphism
`ψ : U₀ ⟶ V` of the underlying objects making the square commute (Stacks 02X1).  Then
`(f^*G)|_{U₀}` is the pullback of `G|_V` along `ψ`, so it is locally projective by Stacks 060M,
and Stacks 060Q propagates that from the one surjective chart to every chart of `X`.

Both steps are unconditional here.  The base-change identity `(f^*G)|_{U₀} ≅ ψ^*(G|_V)` is
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`, and the
quasi-coherence of the chart restrictions which Stacks 060M and Stacks 05JZ require of the
modules they are applied to is
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`; both are consequences of the
identification of a chart restriction with an identity-chart restriction of an étale pullback,
proved in `StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionEtalePullback.lean`.  So
the only hypotheses carried are quasi-coherence of `G`, which Stacks 060S asserts of it, and
local projectivity of its chart restrictions, which is the hypothesis of the tag.

## Main results

* `isLocallyProjective_restrictToChartScheme_of_isSurjective_of_isQuasicoherentOnSite`:
  the substance of Stacks 060Q for a quasi-coherent module, with no carried hypothesis: local
  projectivity of the restriction to one étale chart surjective on points gives it on every
  étale chart.
* `isLocallyProjective_restrictToChartScheme_modulePullback_of_isQuasicoherentOnSite`:
  **Stacks Project, Tag 060S.**

## Implementation notes

**This is the hypothesis-free form of
`AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_modulePullback`**, whose
implementation notes describe the four inputs it carries as binders — Zariski quasi-coherence of
the chart restrictions of `G` and of `f^*G`, the chart comparison for `f^*G`, and the
base-change identity at a commuting square of charts.  Quasi-coherence of `f^*G` on the small
étale site is Stacks 03GA,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, so all
four follow from quasi-coherence of `G` alone.

**The chart comparison is consumed only as an isomorphism, not as an isomorphism of the
canonical map.**  The carried binder `hcart` of
`AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_of_isSurjective` asks that
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` be an isomorphism, and its
proof uses that only to transport local projectivity across it; the discharged form above
therefore takes the existence of *some* isomorphism, which is what
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange` provides, the module on
the other side being produced by the counit of an equivalence of categories.  The one-chart-to-
every-chart step is otherwise the same proof as the carried form and is not derived from it.

**The module universe is the universe `u` of the schemes**, as in
`StacksFrontier/AlgebraicGeometry/Spaces/LocallyProjectiveEtaleChart.lean`: the inverse image of
Stacks 03LU and the comparisons of Stacks 03LW are available only there.

## References

* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
* [Stacks Project, Tag 060M](https://stacks.math.columbia.edu/tag/060M)
* [Stacks Project, Tag 05JZ](https://stacks.math.columbia.edu/tag/05JZ)
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The substance of Stacks Project, Tag 060Q, with its two inputs discharged.**  If the
restriction of a quasi-coherent `𝒪_X`-module to one étale chart surjective on points is locally
projective, then so is its restriction to every étale chart.

The fibre product `W` of the two charts maps to both; `M|_W` is a pullback of `M|_U`, hence
locally projective by Stacks 060M, and it is also a pullback of `M|_V` along a surjective étale,
hence fpqc, covering, so Stacks 05JZ descends local projectivity to `V`.  The two comparisons
are `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange` and the Zariski
quasi-coherence they require is
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`. -/
theorem isLocallyProjective_restrictToChartScheme_of_isSurjective_of_isQuasicoherentOnSite
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS U.1.hom)
    (hU : Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS X.1 X.2 M U))
    (V : SmallEtale B S hS X.1) :
    Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS X.1 X.2 M V) := by
  have : (restrictToChartScheme B S hS X.1 X.2 M U).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS X M hM U
  obtain ⟨W, a, b, hsurja, hetalea⟩ :=
    exists_chart_over_of_isSurjective B S hS X.1 X.2 U hsurj V
  obtain ⟨eb⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS X M hM b
  obtain ⟨ea⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS X M hM a
  have hWproj : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 M W) :=
    Scheme.Modules.isLocallyProjective_of_iso eb
      (pullback_isLocallyProjective (chartSchemeMap b) _ hU)
  exact isLocallyProjective_of_pullback_fpqc _
    (isQuasicoherent_restrictToChartScheme B S hS X M hM V)
    (fun _ : PUnit.{1} => chartScheme W) (fun _ => chartSchemeMap a)
    (ofArrows_mem_fpqcPrecoverage_of_surjective_etale _ hsurja hetalea)
    (fun _ => Scheme.Modules.isLocallyProjective_of_iso ea.symm hWproj)

/-- **Stacks Project, Tag 060S.**  The inverse image of Stacks 03LU of a quasi-coherent
`𝒪_Y`-module whose chart restrictions are locally projective has locally projective chart
restrictions: local projectivity of a quasi-coherent module on an algebraic space is stable
under pullback along an arbitrary morphism of algebraic spaces.

Choose an étale chart `V` of `Y` surjective on points and lift it through `f` to an étale chart
`U₀` of `X` surjective on points with `ψ : U₀ ⟶ V` making the square commute (Stacks 02X1).
Then `(f^*G)|_{U₀}` is the pullback of `G|_V` along `ψ`, so it is locally projective by
Stacks 060M, and Stacks 060Q propagates that to every chart of `X`; quasi-coherence of `f^*G`,
which the latter step needs, is Stacks 03GA. -/
@[stacks 060S]
theorem isLocallyProjective_restrictToChartScheme_modulePullback_of_isQuasicoherentOnSite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite)
    (hproj : ∀ V : SmallEtale B S hS Y.1,
      Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS Y.1 Y.2 G V))
    (U : SmallEtale B S hS X.1) :
    Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U) := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  obtain ⟨U₀, p, ψ, hsq, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V.1.left V.1.hom
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 V.1.left V.1.hom).2 hV)
      V.property
  set U₀c : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hpEtale⟩ with hU₀c
  have hU₀surj : IsSurjective B S hS U₀c.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U₀ p).1 hpSurj
  have : (restrictToChartScheme B S hS Y.1 Y.2 G V).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS Y G hG V
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_modulePullback_square B S hS f G hG U₀c V ψ hsq
  have hU₀proj : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U₀c) :=
    Scheme.Modules.isLocallyProjective_of_iso e.symm
      (pullback_isLocallyProjective ((BigFppfOver.toScheme B S hS).map ψ) _ (hproj V))
  exact isLocallyProjective_restrictToChartScheme_of_isSurjective_of_isQuasicoherentOnSite
    B S hS X ((modulePullback B S hS f).obj G)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG)
    U₀c hU₀surj hU₀proj U

end Space

end AlgebraicGeometry

end
