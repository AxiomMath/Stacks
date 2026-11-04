module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Coherence of the direct image along a finite morphism: the reduction to an étale chart

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with `Y` locally Noetherian, and let `F` be a coherent `𝒪_X`-module.  Stacks
07UH asserts two things: `R^p f_*F = 0` for `p > 0`, and `f_*F` is coherent.  Its proof is a
reduction: choose a scheme `V` and a surjective étale `V ⟶ Y`; then `V ×_Y X ⟶ V` is a finite
morphism of locally Noetherian schemes, and the two assertions follow from the case of schemes
(Cohomology of Schemes, Lemma 01Y6) by the étale base change of Stacks 071Z.

**This file carries out the first step of that reduction for the coherence assertion**, and
assembles that assertion from the reduction and one explicit hypothesis holding the case of a
chart.  The geometry of the base-changed morphism is *discharged* rather than assumed: the base
change of a finite morphism along an étale chart of the target is finite, and the chart is
locally Noetherian when the target is.

The reduction is: coherence of `f_*F` on the small étale ringed site of `Y` is tested on one
étale scheme chart `V` of `Y` surjective on points, which is Stacks 07UB, conditions (1) and
(5), and on such a chart the restriction `(f_*F)|_V` is `f'_*(F|_U)` for `U = V ×_Y X` and `f'`
the base change of `f`, which is Stacks 04CF.  Both inputs are in the library:
`AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective` and
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso`.  The chart is taken to be the
atlas supplied by local Noetherianity of `Y` itself, which is what makes the Noetherian
hypothesis on the chart available with no étale-locality input: see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.isFinite_chartBaseChangeProjection`: **the base change of a finite
  morphism of algebraic spaces along an étale scheme chart of its target is finite.**  This is
  Stacks 03ZS at the chart square.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_chart`: an étale scheme chart of an algebraic
  space, read as an algebraic space, has an étale-local property of schemes as soon as its
  underlying scheme does.  No locality of the property is used.
* `AlgebraicGeometry.Space.isCoherentOnSite_modulePushforward_of_over_of_isSurjective`: the
  reduction itself — `f_*F` is coherent on the small étale ringed site of `Y` as soon as the
  localized direct image `f'_*(F|_U)` of Stacks 04CF is coherent on the slice at one étale
  chart of `Y` surjective on points.  No hypothesis on `f` and none on `F`.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite_of_chartCase`: **the
  coherence assertion of Stacks 07UH, conditional on its chart case**, in the binders of the
  source statement.

## Implementation notes

**No `@[stacks 07UH]` attribute is carried and no part of Stacks 07UH is proved here.**  The
conclusion is reached only from `hchart`, the case of a chart, which holds the whole
mathematical content of the lemma.  That content is the case of schemes, Stacks 01Y6, which
*is* proved for schemes — the coherence half as
`Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite` — but for
`AlgebraicGeometry.Scheme.Modules`, that is for sheaves of modules on the *Zariski* site of a
scheme, and transporting it to the small étale site of the algebraic space represented by that
scheme is not possible in this development: there is no comparison anywhere between
`AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.Space.Modules` of a represented
algebraic space.  The site-level comparison exists
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`) and carries no structure sheaf;
the associated-module functor of Stacks 03DU (4) exists
(`AlgebraicGeometry.SmallEtale.associatedModule`) and is not known to be an equivalence on
quasi-coherent modules, the missing input being Descent, Proposition 03DX (2).  So `hchart` is
owed, and it is owed as a *statement about the small étale site of a chart*, not as the scheme
lemma.

**The vanishing assertion of Stacks 07UH is not treated here, and the reason is not the same.**
Its reduction would need the higher-direct-image analogue of Stacks 04CF in the reading used
below — restriction to the *slice* of the small étale site — whereas what is available is
Stacks 071Z, `AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`, in the
reading where restriction to a chart is `AlgebraicGeometry.Space.etaleModulePullback`; and it
would additionally need that a module whose restriction to a chart surjective on points is zero
is itself zero, which is not in the tree in either reading.  Nothing about the vanishing
assertion is asserted below.

**Why `hchart` may assume local Noetherianity of the chart.**  Local Noetherianity of an
algebraic space is `AlgebraicGeometry.Space.HasEtaleLocalProperty` at the scheme property
`AlgebraicGeometry.IsLocallyNoetherian`, which is Stacks 03E6: the *existence* of a surjective
étale atlas by a locally Noetherian scheme.  Passing from that to local Noetherianity of an
*arbitrary* étale chart is Stacks 03E8 and needs the étale locality of the property, that is
`CategoryTheory.ObjectProperty.IsLocal AlgebraicGeometry.IsLocallyNoetherian
Scheme.etalePrecoverage`, which this tree does not have (it is Stacks 03EA, and the criterion
`AlgebraicGeometry.isLocal_etalePrecoverage_of_affine` is not instantiated at it anywhere).
The proof below therefore does not pass to an arbitrary chart: it takes for `V` the atlas that
the hypothesis `hY` itself supplies, where the property of the underlying scheme is part of the
data, and feeds it to the single-chart form of Stacks 07UB.  That is also exactly the chart the
source's proof chooses.  As a result no étale-locality hypothesis appears in any statement
here.

`hchart` is stated with `f'_*` the localized direct image
`AlgebraicGeometry.Space.chartLocalizedModulePushforward` and `F|_U` restriction to the slice
of the spaces-étale site of `X` at `U`, which is the reading of Stacks 04CF that
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso` delivers.  That is forced, for
the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction`: for a general `f` the
object `U = V ×_Y X` is an algebraic space rather than an étale scheme chart of `X`, so the
restriction cannot be taken on the small étale site of `X`, and the form of Stacks 04CF for a
representable `f`, `AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward`,
is stated for `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which is not compared
with `AlgebraicGeometry.Space.modulePushforward` anywhere.  Finiteness of `f` would make `f`
representable, by Stacks 03ZQ
(`AlgebraicGeometry.Space.isFinite_iff_representable`), so the obstruction is the missing
comparison of the two direct images and not the representability.

Coherence of `F` is carried into `hchart` rather than used in the reduction: the reduction is
an implication between coherence statements about the two direct images and consumes no
property of `F`, exactly as its quasi-coherence counterpart does.

The module universe is the universe `u` of the schemes and not a free one, because
`AlgebraicGeometry.Space.modulePushforward` exists only there; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage`.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The geometry of the base change along an étale chart -/

/-- **Stacks 03ZS for the base change along an étale chart.** The base change of a finite
morphism of algebraic spaces along an étale scheme chart of its target is finite.

This is the first half of the sentence "`V ×_Y X → V` is a finite morphism of locally
Noetherian schemes" with which the proof of Stacks 07UH begins. -/
theorem isFinite_chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hf : IsFinite B S hS f.hom) :
    IsFinite B S hS (chartBaseChangeProjection B S hS f V).hom :=
  isFinite_of_isPullback B S hS
    (isPullback_chartBaseChangeProjection B S hS f V).flip hf

/-- An étale scheme chart of an algebraic space, read as an algebraic space, has an étale-local
property of schemes as soon as its underlying scheme has it: the chart represents it, so the
identity is a surjective étale atlas.

This is the second half of the sentence the proof of Stacks 07UH begins with, at the chart the
proof chooses. Unlike Stacks 03E8 it uses no locality of the property — the property of the
underlying scheme is a hypothesis rather than something deduced from the space — which is why
the main theorem below needs no étale-locality input; see the implementation notes. -/
theorem hasEtaleLocalProperty_chart (P : ObjectProperty Scheme.{u}) (V : SmallEtale B S hS Y.1)
    (hV : P ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))) :
    HasEtaleLocalProperty B S hS
      ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).1 P :=
  hasEtaleLocalProperty_of_representable B S hS _ P _ (Iso.refl _) hV

/-! ### The reduction of the coherence assertion to a chart -/

/-- **The reduction step of the proof of Stacks 07UH, coherence assertion.** The direct image
`f_*F` of an `𝒪_X`-module along a morphism of algebraic spaces is coherent on the small étale
ringed site of `Y` as soon as, for one étale scheme chart `V` of `Y` surjective on points, the
localized direct image `f'_*(F|_U)` of Stacks 04CF is coherent on the slice of the small étale
site of `Y` at `V`.

Coherence is tested on one such chart by Stacks 07UB, conditions (1) and (5),
`AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective`, and the restriction of
`f_*F` to the chart is identified with `f'_*(F|_U)` by Stacks 04CF,
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso`; coherence on a site is
invariant under isomorphism. No hypothesis on `f` and no property of `F` is used. -/
theorem isCoherentOnSite_modulePushforward_of_over_of_isSurjective (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (hsurj : IsSurjective B S hS V.1.hom)
    (h : ((chartLocalizedModulePushforward B S hS f V).obj
      ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsCoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsCoherentOnSite :=
  isCoherentOnSite_of_over_of_isSurjective B S hS Y.1 Y.2 _ V hsurj
    (Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((modulePushforward_comp_overFunctorIso B S hS f V).app F).symm h)

/-- **The coherence assertion of Stacks 07UH, conditional on its chart case.** Let
`f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
let `F` be a coherent `𝒪_X`-module. Then `f_*F` is coherent, granted `hchart`: the same
conclusion for the base change of `f` along an étale scheme chart of `Y` surjective on points,
in the reading of Stacks 04CF.

Finiteness of the base-changed morphism and local Noetherianity of the chart, which `hchart`
takes as hypotheses, are supplied here — by
`AlgebraicGeometry.Space.isFinite_chartBaseChangeProjection` and
`AlgebraicGeometry.Space.hasEtaleLocalProperty_chart` — and so is coherence of `F`. The chart
is the atlas that local Noetherianity of `Y` provides, which is the chart the source's proof
chooses.

**This is not a proof of Stacks 07UH**: `hchart` holds the case of a chart, which is the whole
mathematical content, and no `@[stacks 07UH]` attribute is carried. See the implementation
notes, which record why that case cannot be obtained from the proved case of schemes, and why
the vanishing assertion of the tag is not treated at all. -/
theorem isCoherent_modulePushforward_of_isFinite_of_chartCase (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hchart : ∀ V : SmallEtale B S hS Y.1, IsSurjective B S hS V.1.hom →
      IsFinite B S hS (chartBaseChangeProjection B S hS f V).hom →
      HasEtaleLocalProperty B S hS
        ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).1
        (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
      IsCoherent B S hS X.1 X.2 F →
      ((chartLocalizedModulePushforward B S hS f V).obj
        ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsCoherentOnSite) :
    IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj F) := by
  obtain ⟨U, a, haS, haE, hPU⟩ := hY
  let V : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a, haE⟩
  have hsurj : IsSurjective B S hS V.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 U a).1 haS
  have : ((modulePushforward B S hS f).obj F).IsCoherentOnSite :=
    isCoherentOnSite_modulePushforward_of_over_of_isSurjective B S hS f F V hsurj
      (hchart V hsurj (isFinite_chartBaseChangeProjection B S hS f V hf)
        (hasEtaleLocalProperty_chart B S hS _ V hPU) hF)
  exact isCoherent_of_isCoherentOnSite B S hS Y.1 Y.2 _

end AlgebraicGeometry.Space

end
