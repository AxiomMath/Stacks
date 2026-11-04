module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkFreeness
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresQuotient

/-!
# Stacks 0CZS: a flat geometric fibre stalk makes the module finite free étale locally

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, let `F` be a finitely presented `𝒪_X`-module, let `x̄` be a
geometric point of `X` and let `ȳ = f ∘ x̄`.  Assume `F` is flat at `x` over `Y`.  Stacks 0CZS
says that the following are equivalent:

1. `(F_{ȳ})_{x̄}` is a flat `𝒪_{X_{ȳ}, x̄}`-module,
2. `(F_{ȳ})_{x̄}` is a free `𝒪_{X_{ȳ}, x̄}`-module,
3. `F_{ȳ}` is finite free in an étale neighbourhood of `x̄` in `X_{ȳ}`,
4. `F` is finite free in an étale neighbourhood of `x` in `X`.

`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean` proves the equivalence
of (1) and (2) and, from (1) and the standing flatness, freeness of the geometric stalk `F_{x̄}`
over `𝒪_{X, x̄}`.  This file adds clause (4) and closes the cycle: it descends freeness from the
geometric stalk to the Zariski stalk of an étale scheme chart, trivialises `F` on a Zariski open
of that chart by Stacks 0B8J, and comes back.  So (1), (2) and (4) are equivalent here.

## Main definitions

* `AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint`: clause (4) of Stacks 0CZS — there is
  an étale scheme chart `U ⟶ X` carrying a lift of `x̄`, and a Zariski open `W` of `U` containing
  the point `u` under that lift, on which the restriction of `F` is isomorphic to a free sheaf
  of modules of finite rank.

## Main results

* `Module.Free.quotient_smul_top`: freeness survives reduction modulo an ideal.
* `AlgebraicGeometry.Space.free_geometricModuleStalk_of_free_chartZariskiModuleStalk` and
  `AlgebraicGeometry.Space.flat_chartZariskiModuleStalk_of_flat_geometricModuleStalk`: freeness
  ascends and flatness descends along the comparison of Stacks 05VP.
* `AlgebraicGeometry.Space.free_chartZariskiModuleStalk_iff_free_geometricModuleStalk`: for a
  module of finite presentation on charts, the Zariski stalk of a chart restriction is free over
  the local ring of the chart exactly when the geometric stalk is free over the étale local
  ring.
* `AlgebraicGeometry.Space.exists_over_iso_free_of_free_chartZariskiModuleStalk` and
  `AlgebraicGeometry.Space.free_chartZariskiModuleStalk_of_over_iso_free`: Stacks 0B8J at the
  chart, and its converse.
* `AlgebraicGeometry.Space.isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk`:
  **Stacks 0CZS, (1) implies (4).**
* `AlgebraicGeometry.Space.free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint`:
  **Stacks 0CZS, (4) implies (2).**
* `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_tfae`: **Stacks 0CZS, the equivalence
  of clauses (1), (2) and (4)** under the source's own hypotheses.

Clause (3) is stated elsewhere; see the implementation notes.

## Implementation notes

**How clause (4) is read.**  An étale neighbourhood of `x` in `X` is taken to be a Zariski open
`W` of an étale *scheme* chart `U ⟶ X` of `X`, around a point `u ∈ U` above `x`; finite freeness
is finite freeness of the Zariski restriction `F|_U` on `W`.  This is the source's own reading:
its proof chooses such a chart and applies the scheme-level More on Morphisms, Lemma 37.16.7
(Stacks 080Q) to `F|_U` there.  The lift of `x̄` to the chart is packaged as
`AlgebraicGeometry.Space.SmallEtaleNeighborhood`, whose point `u` is
`AlgebraicGeometry.Space.chartPoint`, and the Zariski restriction is
`AlgebraicGeometry.Space.restrictToChart`; the open `W` is a
`AlgebraicGeometry.Scheme.Opens` of the chart's scheme, and "finite free on `W`" is an
isomorphism of `AlgebraicGeometry.Space.restrictToChart`'s restriction to `W` with
`SheafOfModules.free (ULift (Fin r))`, which is Stacks 03DE (2) read on the Zariski site.

Clause (4) is *not* phrased here with the étale free locus
`AlgebraicGeometry.Space.etaleFiniteFreeLocus` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocus.lean`, which asks for finite freeness of
the inverse image of `F` on the *small étale site* of an algebraic space étale over `X`.  Going
from the Zariski statement proved here to that one is a comparison of two sites — the free
module on the Zariski site of the chart has to be recognised as a free module on the small étale
site of the chart space — and that passage is
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusChartComparison.lean`.  The converse passage,
from the étale-site reading back to a Zariski open of a scheme chart, is not proved.

**Clause (3).**  Clause (3) speaks of an étale neighbourhood of `x̄` inside the geometric fibre
`X_{ȳ}`.  That fibre is `AlgebraicGeometry.Space.geometricFibre` of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreEtaleFreeLocus.lean` — the fibre product of
`f` with the geometric point, formed by Stacks 02X2 in the category of algebraic spaces over `S` —
and clause (3) is
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_geometricFibre_of_isFiniteFreeNearGeometricPoint`
there, obtained from clause (4) as the source obtains it.  What is *not* available is the source's
converse implication `(3) ⟹ (2)`: it identifies the stalk of `F_{ȳ}` at `x̄` on that fibre with the
quotient `F_{x̄} / 𝔪_{ȳ} F_{x̄}` in which clauses (1) and (2) are carried, and that identification
is condition (2) of Stacks 05WY, which
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean` does not state.  So the
equivalence proved here is that of (1), (2) and (4), and clause (3) is a consequence of it rather
than an entry.

**The descent.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean` name the missing input
for `(1) ⟹ (4)` as the descent of flatness along a faithfully flat base change.  It is supplied
here, and it needs nothing new: Stacks 05VP presents the geometric stalk as
`F_{x̄} = (F|_U)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`), the base-change map is faithfully
flat (`AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing`), so flatness of
the geometric stalk over `𝒪_{X, x̄}` gives flatness of the tensor over `𝒪_{U, u}` by transitivity
and then flatness of `(F|_U)_u` over `𝒪_{U, u}` by Stacks 0584 (2),
`Module.Flat.tensorProduct_iff_of_faithfullyFlat`, taken with `S = R`.  The Zariski stalk is
finitely presented over `𝒪_{U, u}`
(`AlgebraicGeometry.Space.finitePresentation_chartZariskiModuleStalk`), and `𝒪_{U, u}` is local,
so flat is free by Stacks 00NZ.  In the other direction no finiteness is needed: a basis of the
Zariski stalk base changes to a basis of the tensor by
`Algebra.TensorProduct.basis`.  The rank-one case of the same descent is
`AlgebraicGeometry.Space.nonempty_linearEquiv_chartZariskiModuleStalk_of_geometricModuleStalk`
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartZariskiStalkRankOneDescent.lean`, which runs
through `Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat` instead; it is not
reproved.

**Stacks 0B8J at the chart.**  The chart restriction `F|_U` is a sheaf of modules on the Zariski
site of the chart's scheme and is of finite presentation there, that being what
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts` says, so Stacks 0B8J applies to it in the
form `Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis`, whose hypothesis is a basis of
the ordinary stalk over the *local ring* of the scheme rather than over the `RingCat`-valued
stalk.  The basis is the chosen basis of the Zariski stalk of Stacks 05VP, carried over by
`AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv` and reindexed by
`Finite.equivFin`; its index type is finite because the stalk is a finite module.  The converse
reads the stalk off a trivialization through
`Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv`, whose input is generating sections of the
restriction with invertible structure map — the generating sections are the images of the
tautological ones under the inverse of the trivializing isomorphism, so that structure map *is*
that inverse.

**Freeness modulo an ideal.**  `Module.Free.quotient_smul_top` is the freeness analogue of
`Module.Flat.quotient_smul_top` of `StacksFrontier/RingTheory/Flat/FibreCriterionNilpotent.lean` and is proved the
same way, through the `A ⧸ J`-linear comparison
`TensorProduct.quotTensorEquivQuotSMulBase` of
`StacksFrontier/RingTheory/Flat/ProjectiveOfIntegralFibresQuotient.lean`; it is what turns freeness
of the geometric stalk into clause (2), the fibre stalk being the reduction of the geometric
stalk modulo `𝔪_{ȳ} 𝒪_{X, x̄}`.

**Hypotheses.**  `(4) ⟹ (2)` uses neither the standing flatness of `F` over `Y`, nor local
finite presentation of `f`, nor finite presentation of `F`: a trivialization on a chart makes the
geometric stalk free outright, and freeness survives the reduction.  `(1) ⟹ (4)` uses all of
them, through `AlgebraicGeometry.Space.free_geometricModuleStalk_of_flat_geometricFibreModuleStalk`
(Stacks 05X0) and through finite presentation of the Zariski stalk.  Finite presentation of `F`
enters in the chartwise form `AlgebraicGeometry.Space.IsFinitePresentationOnCharts`, which the
site form gives by
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`.

The module universe is pinned to the universe `u` of the schemes, as it is in Stacks 05VP and in
`SheafOfModules.free`, whose index type Mathlib declares only in `Type u`.

## References

* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05X0](https://stacks.math.columbia.edu/tag/05X0)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

/-- **Freeness survives reduction modulo an ideal.**  If `M` is a free `A`-module and `J` is an
ideal of `A`, then `M / JM` is a free `A ⧸ J`-module.

This is the freeness analogue of `Module.Flat.quotient_smul_top`, with the same proof: the
reduction is the base change `(A ⧸ J) ⊗_A M` by `TensorProduct.quotTensorEquivQuotSMulBase`, and
a base change of a free module is free. -/
theorem Module.Free.quotient_smul_top (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Free A M] (J : Ideal A) :
    Module.Free (A ⧸ J) (M ⧸ (J • (⊤ : Submodule A M))) :=
  have : Module.Free (A ⧸ J) ((A ⧸ J) ⊗[A] M) := Module.Free.tensor
  Module.Free.of_equiv (TensorProduct.quotTensorEquivQuotSMulBase A M J)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Freeness and flatness across the comparison of Stacks 05VP -/

/-- **Flatness descends from the geometric stalk to the Zariski stalk of a chart.**  If the
geometric stalk `F_{x̄}` of a quasi-coherent `𝒪_X`-module is a flat `𝒪_{X, x̄}`-module, then the
Zariski stalk `(F|_U)_u` of its restriction to an étale scheme chart is a flat
`𝒪_{U, u}`-module.

By Stacks 05VP the geometric stalk is `(F|_U)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`; the base-change map is
faithfully flat, so the tensor is flat over `𝒪_{U, u}` by transitivity and the left factor is
flat over `𝒪_{U, u}` by Stacks 0584 (2).  No finiteness is used. -/
theorem flat_chartZariskiModuleStalk_of_flat_geometricModuleStalk
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite]
    (h : Module.Flat ↥(etaleLocalRing B S hS X.1 xbar)
      ↥(geometricModuleStalk B S hS X xbar F)) :
    Module.Flat ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
  let : Algebra ↥(chartLocalRing B S hS X.1 N) ↥(etaleLocalRing B S hS X.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N).toAlgebra
  have : Module.FaithfullyFlat ↥(chartLocalRing B S hS X.1 N)
      ↥(etaleLocalRing B S hS X.1 xbar) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N
  have hiso := isIso_chartStalkTensorComparison B S hS X.2 N F
  have : Module.Flat ↥(etaleLocalRing B S hS X.1 xbar)
      (↥(etaleLocalRing B S hS X.1 xbar) ⊗[↥(chartLocalRing B S hS X.1 N)]
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) :=
    (Module.Flat.equiv_iff (@asIso _ _ _ _ _ hiso).toLinearEquiv).2 h
  have key : Module.Flat ↥(chartLocalRing B S hS X.1 N)
      (↥(etaleLocalRing B S hS X.1 xbar) ⊗[↥(chartLocalRing B S hS X.1 N)]
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) :=
    Module.Flat.trans _ ↥(etaleLocalRing B S hS X.1 xbar) _
  exact (Module.Flat.tensorProduct_iff_of_faithfullyFlat
    (R := ↥(chartLocalRing B S hS X.1 N)) (S := ↥(chartLocalRing B S hS X.1 N))
    (S' := ↥(etaleLocalRing B S hS X.1 xbar))
    (M := ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F))).1 key

/-- For a quasi-coherent module of finite presentation on charts, the Zariski stalk of a chart
restriction is a free module over the local ring of the chart exactly when the geometric stalk
is a free module over the étale local ring. -/
theorem free_chartZariskiModuleStalk_iff_free_geometricModuleStalk
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    Module.Free ↥(chartLocalRing B S hS X.1 N)
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) ↔
      Module.Free ↥(etaleLocalRing B S hS X.1 xbar)
        ↥(geometricModuleStalk B S hS X xbar F) :=
  ⟨free_geometricModuleStalk_of_free_chartZariskiModuleStalk B S hS N F,
    free_chartZariskiModuleStalk_of_free_geometricModuleStalk B S hS N F hfp⟩

/-! ### Clause (4): finite freeness on a Zariski open of an étale scheme chart -/

/-- **Clause (4) of Stacks 0CZS**: `F` is *finite free in an étale neighbourhood of `x` in `X`*
when there is an étale scheme chart of `X` carrying a lift of the geometric point `x̄`, and a
Zariski open `W` of that chart containing the point `u` under the lift, such that the restriction
of `F` to the chart becomes, on `W`, isomorphic to a free sheaf of modules of finite rank.

This is the reading the source's own proof uses: it passes to a chart and applies the
scheme-level More on Morphisms, Lemma 37.16.7 (Stacks 080Q) there.  Finite freeness is the
condition of Stacks 03DE (2) on the Zariski site of the chart; the étale-site reading, with the
locus `AlgebraicGeometry.Space.etaleFiniteFreeLocus`, is not what is used here. -/
def IsFiniteFreeNearGeometricPoint {X : AlgebraicSpaces B S hS}
    (xbar : GeometricPoint B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (N : SmallEtaleNeighborhood xbar) (r : ℕ) (W : (chartScheme N.chart).Opens),
    chartPoint B S hS X.1 N ∈ W ∧
      Nonempty ((restrictToChart B S hS X.2 F N.chart).over W ≅
        SheafOfModules.free (ULift.{u} (Fin r)))

/-- **Stacks 0B8J at an étale scheme chart.**  If the Zariski stalk of the restriction of a
module of finite presentation on charts to an étale scheme chart is a free module over the local
ring of the chart, then that restriction is isomorphic to a free sheaf of modules of finite rank
on a Zariski open neighbourhood of the point of the chart.

The stalk is finitely presented over the local ring, hence finite, so the chosen basis has a
finite index type and may be reindexed by `ULift (Fin r)`; Stacks 0B8J is then applied in the
form whose hypothesis is a basis over the local ring. -/
theorem exists_over_iso_free_of_free_chartZariskiModuleStalk
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (hfree : Module.Free ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) :
    ∃ (r : ℕ) (W : (chartScheme N.chart).Opens), chartPoint B S hS X.1 N ∈ W ∧
      Nonempty ((restrictToChart B S hS X.2 F N.chart).over W ≅
        SheafOfModules.free (ULift.{u} (Fin r))) := by
  have := hfp N.chart
  have := hfree
  have : Module.FinitePresentation ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
    finitePresentation_chartZariskiModuleStalk B S hS N F hfp
  have : Module.Finite ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := inferInstance
  have hfin : Finite (Module.Free.ChooseBasisIndex ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) := inferInstance
  refine ⟨Nat.card (Module.Free.ChooseBasisIndex ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)), ?_⟩
  have b := ((Module.Free.chooseBasis ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)).reindex
    ((Finite.equivFin _).trans Equiv.ulift.symm)).map
      (chartZariskiModuleStalkStalkEquiv B S hS X.2 N F)
  exact Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis
    (restrictToChart B S hS X.2 F N.chart) (chartPoint B S hS X.1 N) b

/-! ### Stacks 0CZS: clauses (1), (2) and (4) -/

/-- **Stacks 0CZS, (1) implies (4).**  Let `f : X ⟶ Y` be locally of finite presentation, let `F`
be a quasi-coherent `𝒪_X`-module of finite presentation on charts and let `x̄` be a geometric
point of `X`.  If `F` is flat at `x` over `Y` and the fibre stalk `(F_{ȳ})_{x̄}` is a flat
`𝒪_{X_{ȳ}, x̄}`-module, then `F` is finite free in an étale neighbourhood of `x` in `X`.

The route is the source's: clause (1) together with the standing flatness makes the geometric
stalk `F_{x̄}` free over `𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.free_geometricModuleStalk_of_flat_geometricFibreModuleStalk`, which is
Stacks 05X0 at `𝟙 X` over `f`); freeness descends to the Zariski stalk of an étale scheme chart;
and Stacks 0B8J trivialises the chart restriction on a Zariski open of the chart.  The fibre
stalk and its base ring are taken in the quotient form `F_{x̄} / 𝔪_{ȳ} F_{x̄}` over
`𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean`. -/
@[stacks 0CZS "(1) implies (4), with the etale neighbourhood of x taken to be a Zariski open of \
an etale SCHEME chart of X around a point above x and finite freeness read on the Zariski site \
of that chart (the source's own route through More on Morphisms 080Q); the fibre stalk and its \
base ring are in the QUOTIENT FORM F_xbar / m_ybar F_xbar over O_{X, xbar} / m_ybar O_{X, xbar}, \
whose identification with the stalk on the geometric fibre X_ybar is condition (2) of \
Stacks 05WY and is not available"]
theorem isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f F xbar)
    (hfibre : Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f F xbar)) :
    IsFiniteFreeNearGeometricPoint B S hS xbar F := by
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
  have hgeom := free_geometricModuleStalk_of_flat_geometricFibreModuleStalk B S hS f F hf hfp
    xbar hflat hfibre
  obtain ⟨r, W, hW, he⟩ := exists_over_iso_free_of_free_chartZariskiModuleStalk B S hS N F hfp
    (free_chartZariskiModuleStalk_of_free_geometricModuleStalk B S hS N F hfp hgeom)
  exact ⟨N, r, W, hW, he⟩

/-- **Stacks 0CZS, (4) implies (2).**  If `F` is finite free in an étale neighbourhood of `x` in
`X`, then the fibre stalk `(F_{ȳ})_{x̄}` is a free `𝒪_{X_{ȳ}, x̄}`-module.

The trivialization makes the Zariski stalk of the chart restriction free, freeness ascends to the
geometric stalk by Stacks 05VP, and the fibre stalk is the reduction of the geometric stalk
modulo `𝔪_{ȳ} 𝒪_{X, x̄}`.  Neither flatness of `F` over `Y`, nor local finite presentation of
`f`, nor finite presentation of `F` is used, which generalises the source. -/
@[stacks 0CZS "(4) implies (2), with the etale neighbourhood of x a Zariski open of an etale \
SCHEME chart of X and the fibre stalk in the QUOTIENT FORM F_xbar / m_ybar F_xbar over \
O_{X, xbar} / m_ybar O_{X, xbar}; flatness of F over Y, local finite presentation of f and \
finite presentation of F are not assumed"]
theorem free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (xbar : GeometricPoint B S hS X.1)
    (h : IsFiniteFreeNearGeometricPoint B S hS xbar F) :
    Module.Free (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f F xbar) := by
  obtain ⟨N, r, W, hW, ⟨e⟩⟩ := h
  exact free_geometricFibreModuleStalk_of_free_geometricModuleStalk B S hS f F xbar
    (free_geometricModuleStalk_of_free_chartZariskiModuleStalk B S hS N F
      (free_chartZariskiModuleStalk_of_over_iso_free B S hS N F W hW e))

/-- **Stacks 0CZS, the equivalence of clauses (1), (2) and (4).**  Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is locally of finite presentation, let `F` be a finitely
presented quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ`.
If `F` is flat at `x` over `Y`, then

1. `(F_{ȳ})_{x̄}` is a flat `𝒪_{X_{ȳ}, x̄}`-module,
2. `(F_{ȳ})_{x̄}` is a free `𝒪_{X_{ȳ}, x̄}`-module,
4. `F` is finite free in an étale neighbourhood of `x` in `X`

are equivalent.  The fibre stalk and its base ring are taken in the quotient form
`F_{x̄} / 𝔪_{ȳ} F_{x̄}` over `𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}`, which is how the source's own proof
reads clause (1), and clause (4) is read on a Zariski open of an étale scheme chart.  Clause (3)
is not among the entries *here*: it is proved from clause (4) in
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreEtaleFreeLocus.lean`, and it is added to the
equivalence — in its Zariski-chart reading on the geometric fibre, together with clauses (1) and
(2) in their literal form on that fibre — by
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_geometricFibre_tfae` of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkClauseThree.lean`.  The source's reverse
implication `(3) ⟹ (2)` goes through the identification of the stalk on the geometric fibre with
the quotient, which is condition (2) of Stacks 05WY and is still not available; the equivalence
does not need it, only the agreement of the two flatness conditions across the cartesian defining
square of the fibre. -/
@[stacks 0CZS "clauses (1), (2) and (4) are equivalent, under the source's own hypotheses, with \
the fibre stalk and its base ring in the QUOTIENT FORM F_xbar / m_ybar F_xbar over \
O_{X, xbar} / m_ybar O_{X, xbar} and clause (4) read as finite freeness on a Zariski open of an \
etale SCHEME chart of X around a point above x"]
theorem flat_geometricFibreModuleStalk_tfae
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFinitePresentationOnSite F]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f F xbar) :
    [Module.Flat (geometricFibreLocalRing B S hS f xbar)
        (geometricFibreModuleStalk B S hS f F xbar),
      Module.Free (geometricFibreLocalRing B S hS f xbar)
        (geometricFibreModuleStalk B S hS f F xbar),
      IsFiniteFreeNearGeometricPoint B S hS xbar F].TFAE := by
  have hfp : IsFinitePresentationOnCharts B S hS X.2 F :=
    isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F inferInstance
      inferInstance
  tfae_have 1 → 3 := fun h =>
    isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk B S hS f F hf hfp xbar
      hflat h
  tfae_have 3 → 2 := fun h =>
    free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint B S hS f F xbar h
  tfae_have 2 → 1 := fun h => flat_geometricFibreModuleStalk_of_free B S hS f F xbar h
  tfae_finish

end AlgebraicGeometry.Space

end
