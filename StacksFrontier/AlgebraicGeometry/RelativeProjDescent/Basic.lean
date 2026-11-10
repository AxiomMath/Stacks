module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.Generic
public import StacksFrontier.AlgebraicGeometry.TrivializingSite.Basic

/-!
# Glueing chart isomorphisms of two relative `Proj`s over a trivializing cover

Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras in the sense of
Situation 01NN and let `ℒ` be an invertible `𝒪_S`-module. Suppose that over every affine open `W`
of `S` on which `ℒ` is trivial the chart of `Proj_S(B)` over `W` has been identified with the
chart of `Proj_S(A)` over `W`, compatibly with the structure morphisms to `S` and with the
transition morphisms of the charts. **Then `Proj_S(B) ≅ Proj_S(A)` over `S`.**

This file isolates that descent step, with the chart isomorphisms as *data*. No property of `A`
or `B` beyond being graded algebra data enters, and `ℒ` enters only through the index category
`Stacks.AlgebraicGeometry.TrivializingSite.Site` of its trivializing affine opens: all the file
uses about that category is that the charts over its objects form a locally directed open cover
of the relative homogeneous spectrum, which is
`Stacks.AlgebraicGeometry.TrivializingSite.trivCover`.

Two instances are consumed downstream: the twist `B = A ⊗ ℒ^{⊗ •}` of Tag 02NB, in
`StacksFrontier/AlgebraicGeometry/RelativeProjTwist/Basic.lean`, and the projective bundle of a
tensor product `𝐏(E ⊗ ℒ) ≅ 𝐏(E)`, in
`StacksFrontier/AlgebraicGeometry/SymProjectiveBundleTwist/Basic.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjDescent.chartMor`: a chart isomorphism, read as a
  morphism into `Proj_S(A)`.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.desc`: the glued morphism
  `Proj_S(B) ⟶ Proj_S(A)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjDescent.exists_iso_relativeProj_of_chartIso`: **the
  descent statement.** Chart isomorphisms over the trivializing affine opens, compatible with the
  structure morphisms to `S` and natural in the open, glue to an isomorphism
  `Proj_S(B) ≅ Proj_S(A)` of schemes over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.chart_desc`: on the chart over a trivializing
  affine open the glued morphism is the given chart isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.isPullback_chart_desc`: that identification is
  cartesian, which is what makes the glued morphism an isomorphism.

## Implementation notes

**Why the glueing needs no cocycle condition.** The charts over the trivializing affine opens
form a *locally directed* open cover: the intersection of two of them is covered by further
members of the same family, because a trivializing affine open can be found inside any open
around any point (`Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible`). For such
a cover `AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected` asks only for
compatibility along the arrows of the index category, which is the `hnat` hypothesis below.

**Why the naturality hypothesis is phrased with `chartFunctor`.** The transition map of
`trivCover` is `GradedAlgebra.transition` of the inclusion of opens, which is definitionally
`(chartFunctor _).map` of the arrow of the site but not syntactically so; the two are bridged by
`show` inside `trans_chartMor`, never by `rw`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/TrivializingSite/Basic.lean`. The `chartFunctor` spelling is the
one in which a caller's naturality square is naturally stated.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.TrivializingSite

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjDescent

variable {S : Scheme.{u}} {A B : RelativeProj.GradedAlgebra S} (L : S.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (ε : ∀ W : Site L, B.projOver W.1 ≅ A.projOver W.1)

/-- **A chart isomorphism, read as a morphism into `Proj_S(A)`**: the identification of the chart
of `Proj_S(B)` over a trivializing affine open with the chart of `Proj_S(A)` over it, followed by
that chart. -/
def chartMor (W : Site L) : B.projOver W.1 ⟶ relativeProj A :=
  (ε W).hom ≫ chart A W.1

/-- **The chart isomorphisms are compatible with the transition morphisms of the cover.** This is
the naturality hypothesis, together with the compatibility of the charts of `Proj_S(A)` with its
transitions. -/
theorem trans_chartMor
    (hnat : ∀ {W W' : Site L} (h : W ⟶ W'),
      (ε W).hom ≫ (chartFunctor A).map (Site.homVal h) =
        (chartFunctor B).map (Site.homVal h) ≫ (ε W').hom)
    {W W' : Site L} (h : W ⟶ W') :
    (trivCover B L).trans h ≫ chartMor L ε W' = chartMor L ε W := by
  have hw : (chartFunctor A).map (Site.homVal h) ≫ chart A W'.1 = chart A W.1 :=
    transition_comp_chart A (Site.homVal h)
  change (chartFunctor B).map (Site.homVal h) ≫ (ε W').hom ≫ chart A W'.1 =
      (ε W).hom ≫ chart A W.1
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ chart A W'.1) (hnat h).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun g => (ε W).hom ≫ g) hw)))

variable (hbase : ∀ W : Site L, (ε W).hom ≫ A.toBase W.1 = B.toBase W.1)
  (hnat : ∀ {W W' : Site L} (h : W ⟶ W'),
    (ε W).hom ≫ (chartFunctor A).map (Site.homVal h) =
      (chartFunctor B).map (Site.homVal h) ≫ (ε W').hom)

/-- **The glued morphism `Proj_S(B) ⟶ Proj_S(A)`.** The charts over the trivializing affine opens
form a locally directed open cover of `Proj_S(B)`, so the chart isomorphisms glue as soon as they
are compatible with the transitions. -/
def desc : relativeProj B ⟶ relativeProj A :=
  (trivCover B L).glueMorphismsOfLocallyDirected (chartMor L ε)
    (fun {_ _} h => trans_chartMor L ε hnat h)

/-- On the chart over a trivializing affine open the glued morphism is the chart isomorphism. -/
theorem chart_desc (W : Site L) :
    chart B W.1 ≫ desc L ε hnat = chartMor L ε W :=
  (trivCover B L).map_glueMorphismsOfLocallyDirected (chartMor L ε)
    (fun {_ _} h => trans_chartMor L ε hnat h) W

include hbase in
/-- **The glued morphism is a morphism over `S`.** On each chart it is the chart isomorphism,
which carries the structure morphism of one chart to the structure morphism of the other. -/
theorem desc_relativeProjToBase :
    desc L ε hnat ≫ relativeProjToBase A = relativeProjToBase B := by
  refine (trivCover B L).hom_ext _ _ fun W => ?_
  rw [trivCover_f, ← Category.assoc, chart_desc, chartMor, Category.assoc,
    chart_relativeProjToBase, hbase W, chart_relativeProjToBase]

include hbase in
/-- The preimage of a chart of `Proj_S(A)` over a trivializing affine open under the glued
morphism is the chart of `Proj_S(B)` over the same affine open. -/
theorem desc_preimage_opensRange_chart (W : Site L) :
    desc L ε hnat ⁻¹ᵁ (chart A W.1).opensRange = (chart B W.1).opensRange := by
  rw [opensRange_chart, opensRange_chart, ← Scheme.Hom.comp_preimage,
    desc_relativeProjToBase L ε hbase hnat]

include hbase in
/-- **Over the chart of a trivializing affine open the glued morphism is the chart isomorphism,
cartesianly.** Both charts are open immersions, the square commutes, and the preimage of the range
of one is the range of the other, which is what makes the square cartesian. -/
theorem isPullback_chart_desc (W : Site L) :
    IsPullback (chart B W.1) (ε W).hom (desc L ε hnat) (chart A W.1) :=
  (IsOpenImmersion.isPullback (ε W).hom (chart B W.1) (chart A W.1) (desc L ε hnat)
    ((chart_desc L ε hnat W).trans (congrArg (fun f => f ≫ chart A W.1) rfl))
    (desc_preimage_opensRange_chart L ε hbase hnat W)).flip

/-- The preimages of the trivializing affine opens cover `Proj_S(A)`. -/
theorem iSup_preimage_toOpens_eq_top :
    (⨆ W : Site L, relativeProjToBase A ⁻¹ᵁ W.1.toOpens) = (⊤ : (relativeProj A).Opens) := by
  have h2 : relativeProjToBase A ⁻¹ᵁ (⨆ W : Site L, W.1.toOpens) =
      ⨆ W : Site L, relativeProjToBase A ⁻¹ᵁ W.1.toOpens :=
    TopologicalSpace.Opens.map_iSup _ _
  rw [← h2, iSup_toOpens_eq_top]
  simp

include hbase in
/-- **The glued morphism is an isomorphism.** Being an isomorphism is Zariski-local on the
target, the preimages of the trivializing affine opens cover `Proj_S(A)`, and over each of them
the glued morphism is pulled back to a chart isomorphism. -/
theorem isIso_desc : IsIso (desc L ε hnat) :=
  Stacks.AlgebraicGeometry.ProjBaseChange.isIso_of_isPullback_cover (desc L ε hnat)
    (fun W : Site L => relativeProjToBase A ⁻¹ᵁ W.1.toOpens)
    (iSup_preimage_toOpens_eq_top L (A := A))
    (fun W => A.projOver W.1) (fun W => chart A W.1) (fun _ => inferInstance)
    (fun W => congrArg
      (fun V : (relativeProj A).Opens => (V : Set (relativeProj A)))
      (opensRange_chart A W.1))
    (fun W => B.projOver W.1) (fun W => chart B W.1) (fun W => (ε W).hom)
    (fun W => isPullback_chart_desc L ε hbase hnat W) (fun _ => inferInstance)

include hbase hnat in
/-- **Chart isomorphisms over the trivializing affine opens of an invertible module glue to an
isomorphism of the relative homogeneous spectra over the base.**

Given quasi-coherent graded `𝒪_S`-algebras `A` and `B`, an invertible `𝒪_S`-module `ℒ`, and for
every affine open `W` of `S` trivializing `ℒ` an isomorphism `ε W` of the chart of `Proj_S(B)`
over `W` with the chart of `Proj_S(A)` over `W` which

* carries the structure morphism of the chart of `Proj_S(A)` to that of the chart of `Proj_S(B)`
  (`hbase`), and
* commutes with the transition morphisms of the charts (`hnat`),

there is an isomorphism `Proj_S(B) ≅ Proj_S(A)` compatible with the two structure morphisms
to `S`. The isomorphism is the glued morphism
`Stacks.AlgebraicGeometry.RelativeProjDescent.desc`, which restricts to `ε W` on the chart over
`W` by `Stacks.AlgebraicGeometry.RelativeProjDescent.chart_desc`. -/
theorem exists_iso_relativeProj_of_chartIso :
    ∃ f : relativeProj B ≅ relativeProj A,
      f.hom ≫ relativeProjToBase A = relativeProjToBase B :=
  ⟨@asIso _ _ _ _ (desc L ε hnat) (isIso_desc L ε hbase hnat),
    desc_relativeProjToBase L ε hbase hnat⟩

end Stacks.AlgebraicGeometry.RelativeProjDescent

end
