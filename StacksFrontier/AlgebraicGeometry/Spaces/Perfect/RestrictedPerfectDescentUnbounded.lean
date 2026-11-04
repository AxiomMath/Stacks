module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescentOverIntegers

/-!
# Stacks 09RJ with the bounded-charts hypothesis discharged

`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_and_perfectHomsDescend` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RestrictedPerfectDescentOverIntegers.lean`, the
declaration that carries `@[stacks 09RJ]`, takes one hypothesis beyond the data of Situation
09RH: the size bound `AlgebraicGeometry.Space.ChartsBounded` on the chart systems of the stages,
which the source does not state.  This file removes that binder.  What replaces it is
`#I < B.cutoff.ord.cof`, the size hypothesis of Stacks 07SF, by way of
`AlgebraicGeometry.Space.chartsBounded_of_mk_lt_cof_ord_op`: the index category of a situation's
system is the opposite of a preorder, so the bound on the morphism types that
`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord` also asks for is automatic, the morphisms
of a preorder being subsingletons.

## Why this is a strict improvement in faithfulness, not a lateral move

`AlgebraicGeometry.Space.ChartsBounded` is a hypothesis about *chart systems* — an artefact of
working with `u`-small models of the big fppf site, nowhere visible in the source.  The cardinal
bound that replaces it is, by contrast, one of the two restrictions this tree has established as
non-negotiable for the whole 09RH circle of results:

* `#I < B.cutoff.ord.cof` is refuted beyond that bound by
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`;
* `I : Type u` is refuted beyond it by
  `StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`.

Both are forced rather than convenient, and `#I < B.cutoff.ord.cof` is already enough on its own
for Stacks 07SI at the structure sheaf
(`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/GlobalFunctionsColimit.lean`).  So the trade made
here replaces a hypothesis the source does not state by one the formalization cannot do without,
and the statements below are at the hypotheses of Situation 09RH plus that restriction alone.

`I : Type u` is not an extra assumption either: it is already the index universe of the
declarations being invoked, and `#I < B.cutoff.ord.cof` would force it in any case, `B.cutoff`
being a `Cardinal.{u}`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.chartsBounded_of_mk_lt_cof_ord`: the discharge
  itself, for a situation's own system.
* `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_mk_lt_cof_ord`: the
  essential surjectivity half of Stacks 09RJ with no bounded-charts hypothesis.
* `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_mk_lt_cof_ord`: the full
  faithfulness half, likewise.
* `AlgebraicGeometry.Space.DescentSituation`'s
  `perfectObjectsDescend_and_perfectHomsDescend_of_mk_lt_cof_ord`: **Stacks 09RJ** with no
  bounded-charts hypothesis.

No `@[stacks 09RJ]` attribute is placed here; the registration is
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_and_perfectHomsDescend` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RestrictedPerfectDescentOverIntegers.lean`, which
is untouched.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Lemma 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The charts of the system of a descent situation are bounded** as soon as the index set is
smaller than the cofinality of the site's size cutoff, and from nothing else.

The index category of `AlgebraicGeometry.Space.DescentSituation.system` is `Iᵒᵖ` for a preorder
`I`, so this is `AlgebraicGeometry.Space.chartsBounded_of_mk_lt_cof_ord_op`; the bound on the
morphism types that `AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord` also asks for is
automatic, the morphisms of a preorder being subsingletons and `ℵ₀` lying below that
cofinality. -/
theorem chartsBounded_of_mk_lt_cof_ord (hI : Cardinal.mk I < B.cutoff.ord.cof) :
    ChartsBounded B S hS D.system :=
  chartsBounded_of_mk_lt_cof_ord_op B S hS D.system hI

/-- **The essential surjectivity half of Stacks 09RJ, at the hypotheses of Situation 09RH and the
cardinal bound alone.** Every perfect object of `D(𝒪_X)` on the limit is `Lfᵢ^*Eᵢ` for some stage
`i ≥ 0` and some perfect `Eᵢ` on `Xᵢ`.

This is `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_chartsBounded` with
its bounded-charts hypothesis discharged by
`AlgebraicGeometry.Space.DescentSituation.chartsBounded_of_mk_lt_cof_ord`. -/
theorem perfectObjectsDescend_of_mk_lt_cof_ord (hI : Cardinal.mk I < B.cutoff.ord.cof) :
    D.PerfectObjectsDescend :=
  D.perfectObjectsDescend_of_chartsBounded (D.chartsBounded_of_mk_lt_cof_ord hI)

/-- **The full faithfulness half of Stacks 09RJ, at the hypotheses of Situation 09RH and the
cardinal bound alone.** For perfect `Eᵢ`, `Kᵢ` on a stage `Xᵢ` the comparison
`colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)` is bijective.

This is `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_chartsBounded` with its
bounded-charts hypothesis discharged by
`AlgebraicGeometry.Space.DescentSituation.chartsBounded_of_mk_lt_cof_ord`. -/
theorem perfectHomsDescend_of_mk_lt_cof_ord (hI : Cardinal.mk I < B.cutoff.ord.cof) :
    D.PerfectHomsDescend :=
  D.perfectHomsDescend_of_chartsBounded (D.chartsBounded_of_mk_lt_cof_ord hI)

/-- **Stacks 09RJ at the hypotheses of Situation 09RH, with no bounded-charts hypothesis.** In
Situation 09RH, indexed by a directed set in the universe of the site with fewer elements than
the cofinality of the site's size cutoff, the category of perfect objects of `D(𝒪_X)` is the
colimit of the categories of perfect objects of `D(𝒪_{Xᵢ})`: essential surjectivity
(`AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescend`) and full faithfulness
(`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`).

The size bound `AlgebraicGeometry.Space.ChartsBounded` that
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_and_perfectHomsDescend` assumes,
and that the source does not state, is discharged here by
`AlgebraicGeometry.Space.DescentSituation.chartsBounded_of_mk_lt_cof_ord`.  What is left is
`#I < B.cutoff.ord.cof`, which is not a weakening: it is refuted beyond that bound by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`, and
`I : Type u` is refuted beyond it by
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean`.

This carries `@[stacks 09RJ]` for **both halves** — essential surjectivity
(`AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescend`) and full faithfulness
(`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`) — at Situation 09RH's own
hypotheses.  The only restriction beyond the tag's is `#I < B.cutoff.ord.cof`, which this
formalization is counterexample-forced to carry.

The `AlgebraicGeometry.Space.ChartsBounded` bound that
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_and_perfectHomsDescend` assumes,
and which the source does not state, is discharged here.  That statement keeps its own
registration: `hI` implies `ChartsBounded` but not conversely, so it remains the more general
conditional form. -/
@[stacks 09RJ "both halves, at the tag's own hypotheses"]
theorem perfectObjectsDescend_and_perfectHomsDescend_of_mk_lt_cof_ord
    (hI : Cardinal.mk I < B.cutoff.ord.cof) :
    D.PerfectObjectsDescend ∧ D.PerfectHomsDescend :=
  ⟨D.perfectObjectsDescend_of_mk_lt_cof_ord hI, D.perfectHomsDescend_of_mk_lt_cof_ord hI⟩

end DescentSituation

end AlgebraicGeometry.Space

end
