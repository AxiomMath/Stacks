module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.RelativeProjDescent.Basic
public import StacksFrontier.AlgebraicGeometry.TwistChart.Basic

/-!
# Twisting a graded algebra by an invertible module does not change the relative `Proj`

Let `S` be a scheme, let `𝒜` be a quasi-coherent graded `𝒪_S`-algebra in the sense of Situation
01NN and let `ℒ` be an invertible `𝒪_S`-module. The twist `ℬ = 𝒜 ⊗ ℒ` of Tag 02NB has
`ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`
(`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`), and this file proves the
isomorphism-over-`S` part of [Stacks, Tag 02NC] on the relative homogeneous spectrum of
`Stacks.AlgebraicGeometry.RelativeProjGlue`: the relative homogeneous spectra of `ℬ` and of `𝒜`
are isomorphic as schemes over `S`. The whole tag, with clauses (1) and (2), is stated on the
other relative homogeneous spectrum, `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, as
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`.

The source's argument is *"This is the identity map when `ℒ ≅ 𝒪_S`. In general choose an open
covering of `S` such that `ℒ` is trivialized over the pieces and glue the corresponding maps."*
That is exactly what happens here. On an affine open `W` of `S` trivializing `ℒ` the graded ring
of sections of `ℬ` is the graded ring of sections of `𝒜`
(`Stacks.AlgebraicGeometry.TwistChart.chartRingEquiv`), so the two charts of the relative Proj
over `W` are identified (`Stacks.AlgebraicGeometry.TwistChart.chartProjIso`); the identification
does not depend on the trivialization chosen and commutes with restriction to a smaller
trivializing open, and the charts over the trivializing affine opens form a locally directed open
cover of the relative Proj
(`Stacks.AlgebraicGeometry.TrivializingSite.trivCover`), along which the chart identifications
glue.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwist.chartIso`: the comparison on the chart over a
  trivializing affine open.
* `Stacks.AlgebraicGeometry.RelativeProjTwist.twistDesc`: the glued comparison morphism
  `Proj_S(ℬ) ⟶ Proj_S(𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjTwist.relativeProjTwistIso`: **the isomorphism
  `Proj_S(𝒜 ⊗ ℒ) ≅ Proj_S(𝒜)`.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwist.exists_iso_relativeProjToBase_twist`: the
  isomorphism-over-`S` part of Tag 02NC — for a quasi-coherent graded `𝒪_S`-algebra `𝒜` and an
  invertible `𝒪_S`-module `ℒ` there is an isomorphism `Proj_S(𝒜 ⊗ ℒ) ≅ Proj_S(𝒜)` compatible
  with the two structure morphisms to `S`. The whole tag is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`.
* `Stacks.AlgebraicGeometry.RelativeProjTwist.twistDesc_relativeProjToBase`: the glued morphism
  is a morphism over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjTwist.isPullback_chart_twistDesc`: over the chart of a
  trivializing affine open the glued morphism is the chart comparison, cartesianly; this is what
  makes it an isomorphism, being an isomorphism Zariski-locally on the target.

## Implementation notes

**The glueing is not done here.** It is
`Stacks.AlgebraicGeometry.RelativeProjDescent.exists_iso_relativeProj_of_chartIso`, which takes
the chart isomorphisms as data and asks exactly for the two compatibilities below; nothing in
this file knows how a locally directed cover is glued. What remains here is the instantiation:
the chart isomorphism of Tag 02NB and its two compatibilities.

**Where the choice of trivialization goes.** A trivializing affine open carries no *chosen*
trivialization — `Stacks.AlgebraicGeometry.TrivializingSite.IsTrivializing` is a `Nonempty`, and
`triv` picks a representative. That is harmless exactly because
`Stacks.AlgebraicGeometry.TwistChart.chartProjIso_eq` says the chart comparison does not depend
on the representative, which is also what lets the naturality lemma compare the comparison over a
smaller open with the restriction of the one over the larger.

**Two spellings of invertibility.** The twist of Tag 02NB is stated for
`Stacks.SheafOfModules.IsInvertible` and the local triviality of Tag 0B8M for
`AlgebraicGeometry.SheafOfModules.IsInvertible`. They are the same statement about the same data,
by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; the `local instance` below is that
theorem, so that one hypothesis serves both and the statement of the tag mentions only one.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist (twist)
open Stacks.AlgebraicGeometry.TrivializingSite
open Stacks.AlgebraicGeometry.TwistChart

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwist

/-- The invertibility predicate of Tag 0B8M from the one of Tag 01CS: the two are the same
statement about the same data, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. Local, so that the library keeps
exactly one invertibility hypothesis in scope elsewhere. -/
local instance isInvertible_toAlgebraicGeometry {S : Scheme.{u}} {L : S.Modules}
    [h : Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L h

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- A trivialization of `ℒ` over a trivializing affine open of `S`. Which one is chosen does not
matter: `Stacks.AlgebraicGeometry.TwistChart.chartProjIso_eq`. -/
def triv (W : Site L) :
    L.over W.1.toOpens ≅ SheafOfModules.unit (S.ringCatSheaf.over W.1.toOpens) :=
  W.2.some

/-- **The chart isomorphism over a trivializing affine open**: the identification of the chart of
`Proj_S(ℬ)` over `W` with the chart of `Proj_S(𝒜)` over `W`, for the chosen trivialization. -/
def chartIso (W : Site L) :
    (twist 𝒜 L).toGradedAlgebra.projOver W.1 ≅ 𝒜.toGradedAlgebra.projOver W.1 :=
  chartProjIso 𝒜 L W.1 (triv L W)

/-- **Each chart isomorphism is an isomorphism over the base.** -/
theorem chartIso_hom_toBase (W : Site L) :
    (chartIso 𝒜 L W).hom ≫ 𝒜.toGradedAlgebra.toBase W.1 =
      (twist 𝒜 L).toGradedAlgebra.toBase W.1 :=
  chartProjIso_hom_toBase 𝒜 L W.1 (triv L W)

/-- **The chart isomorphisms are natural in the trivializing affine open.** The trivialization
chosen over the smaller open may be replaced by the restriction of the one over the larger,
because the chart comparison does not depend on the trivialization
(`Stacks.AlgebraicGeometry.TwistChart.chartProjIso_eq`). -/
theorem chartIso_naturality {W W' : Site L} (h : W ⟶ W') :
    (chartIso 𝒜 L W).hom ≫ (chartFunctor 𝒜.toGradedAlgebra).map (Site.homVal h) =
      (chartFunctor (twist 𝒜 L).toGradedAlgebra).map (Site.homVal h) ≫ (chartIso 𝒜 L W').hom :=
  chartProjIso_naturality 𝒜 L W'.1 W.1 (Site.homVal h) (triv L W') (triv L W)

/-- **The glued comparison morphism `Proj_S(ℬ) ⟶ Proj_S(𝒜)`.** The charts over the trivializing
affine opens form a locally directed open cover of `Proj_S(ℬ)`, so the chart isomorphisms glue as
soon as they are compatible with the transitions. -/
def twistDesc : relativeProj (twist 𝒜 L).toGradedAlgebra ⟶ relativeProj 𝒜.toGradedAlgebra :=
  RelativeProjDescent.desc L (chartIso 𝒜 L) (fun {_ _} h => chartIso_naturality 𝒜 L h)

/-- On the chart over a trivializing affine open the glued morphism is the chart isomorphism. -/
theorem chart_twistDesc (W : Site L) :
    chart (twist 𝒜 L).toGradedAlgebra W.1 ≫ twistDesc 𝒜 L =
      (chartIso 𝒜 L W).hom ≫ chart 𝒜.toGradedAlgebra W.1 :=
  RelativeProjDescent.chart_desc L (chartIso 𝒜 L) (chartIso_naturality 𝒜 L) W

/-- **The glued morphism is a morphism over `S`.** On each chart it is the chart isomorphism,
which carries the structure morphism of one chart to the structure morphism of the other. -/
theorem twistDesc_relativeProjToBase :
    twistDesc 𝒜 L ≫ relativeProjToBase 𝒜.toGradedAlgebra =
      relativeProjToBase (twist 𝒜 L).toGradedAlgebra :=
  RelativeProjDescent.desc_relativeProjToBase L (chartIso 𝒜 L) (chartIso_hom_toBase 𝒜 L)
    (chartIso_naturality 𝒜 L)

/-- **Over the chart of a trivializing affine open the glued morphism is the chart isomorphism,
cartesianly.** This is what makes it an isomorphism, being an isomorphism Zariski-locally on the
target. -/
theorem isPullback_chart_twistDesc (W : Site L) :
    IsPullback (chart (twist 𝒜 L).toGradedAlgebra W.1) (chartIso 𝒜 L W).hom (twistDesc 𝒜 L)
      (chart 𝒜.toGradedAlgebra W.1) :=
  RelativeProjDescent.isPullback_chart_desc L (chartIso 𝒜 L) (chartIso_hom_toBase 𝒜 L)
    (chartIso_naturality 𝒜 L) W

/-- **The glued morphism is an isomorphism.** Being an isomorphism is Zariski-local on the
target, the preimages of the trivializing affine opens cover `Proj_S(𝒜)`, and over each of them
the glued morphism is pulled back to the chart isomorphism. -/
instance isIso_twistDesc : IsIso (twistDesc 𝒜 L) :=
  RelativeProjDescent.isIso_desc L (chartIso 𝒜 L) (chartIso_hom_toBase 𝒜 L)
    (fun {_ _} h => chartIso_naturality 𝒜 L h)

/-- **The isomorphism `Proj_S(𝒜 ⊗ ℒ) ≅ Proj_S(𝒜)`**, the isomorphism-over-`S` part of
[Stacks, Tag 02NC]; the whole tag is
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`. -/
def relativeProjTwistIso :
    relativeProj (twist 𝒜 L).toGradedAlgebra ≅ relativeProj 𝒜.toGradedAlgebra :=
  asIso (twistDesc 𝒜 L)

/-- **The isomorphism-over-`S` part of [Stacks, Tag 02NC].** For a scheme `S`, a quasi-coherent
graded `𝒪_S`-algebra `𝒜` and an invertible `𝒪_S`-module `ℒ`, the relative homogeneous spectrum
of the twist `ℬ = 𝒜 ⊗ ℒ`, whose degree-`d` piece is `𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`, is isomorphic to the
relative homogeneous spectrum of `𝒜`, by an isomorphism of schemes over `S`: it carries the
structure morphism `Proj_S(𝒜) ⟶ S` to the structure morphism `Proj_S(ℬ) ⟶ S`.

The isomorphism is `Stacks.AlgebraicGeometry.RelativeProjTwist.relativeProjTwistIso`; over the
chart of an affine open trivializing `ℒ` it is the chart comparison
`Stacks.AlgebraicGeometry.TwistChart.chartProjIso`, by
`Stacks.AlgebraicGeometry.RelativeProjTwist.chart_twistDesc`. The whole tag, with clauses (1)
and (2), is `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`. -/
theorem exists_iso_relativeProjToBase_twist :
    ∃ f : relativeProj (twist 𝒜 L).toGradedAlgebra ≅ relativeProj 𝒜.toGradedAlgebra,
      f.hom ≫ relativeProjToBase 𝒜.toGradedAlgebra =
        relativeProjToBase (twist 𝒜 L).toGradedAlgebra :=
  ⟨relativeProjTwistIso 𝒜 L, twistDesc_relativeProjToBase 𝒜 L⟩

end Stacks.AlgebraicGeometry.RelativeProjTwist

end
