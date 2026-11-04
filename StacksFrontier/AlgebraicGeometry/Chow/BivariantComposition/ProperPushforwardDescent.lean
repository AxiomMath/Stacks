module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# Proper pushforward descends to Chow groups: the bundled hypothesis, discharged

`Stacks.Chow.ProperPushforwardDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic` bundles Stacks 02S2 over all of
its inputs: it asserts that for every pair of schemes locally of finite type over the base, every
proper morphism between them over the base and every degree, proper pushforward of cycles carries
cycles rationally equivalent to zero to cycles rationally equivalent to zero. Being a `Pi` into
`Prop` it is itself a `Prop`, and the bivariant development takes it as a hypothesis in that
bundled shape because a bivariant class caps with test morphisms that are produced inside the
construction, so the morphisms Stacks 02S2 is needed for are not available to be named in advance.

The hypothesis is not open. Stacks 02S2 is proved in this repository for an arbitrary proper
morphism over the base, as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence` in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications`, and so
the bundled form is a theorem: that is `Stacks.Chow.properPushforwardDescends` below.

This file exists only to join the two. `Stacks.Chow.ProperPushforwardDescends` is stated far
upstream of its proof — the module stating it has an import closure of 358 modules and 37
dependents, while the proof needs 1694 — so discharging it where it is stated would push some
fourteen hundred modules into every one of those dependents. Proving it in a downstream leaf
instead costs nothing to anybody: a consumer that wants the theorem rather than the hypothesis
imports this module, and a consumer that does not is unaffected.

## Main results

* `Stacks.Chow.properPushforwardDescends` — `Stacks.Chow.ProperPushforwardDescends` holds for
  every `Stacks.Chow.ChowSituation`.

## Implementation notes

The proof reads
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence` rather than the tagged
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre`. The two statements
are the same; the former has the smaller import closure of the two, 1694 modules against 1907, and
nothing else here needs the generic-fibre material.

No `@[stacks 02S2]` attribute is attached. Stacks 02S2 is already carried, in both of its forms,
by `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` and
`Stacks.Chow.properPushforward_rationallyEquivalent_of_isProper`; the statement below adds no
mathematical content to them, it only quantifies over the inputs they are already universally
quantified over, so tagging it would double-count the tag rather than extend its coverage.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 02S2, bundled over all of its inputs.** For every base situation, proper pushforward
of cycles along every proper morphism over the base, in every degree, carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero.

This is `Stacks.Chow.ProperPushforwardDescends`, the hypothesis the bivariant development of
Stacks 0B76 carries, proved outright. A consumer that can reach this module should supply it
instead of assuming it. -/
theorem properPushforwardDescends (C : ChowSituation.{u}) : ProperPushforwardDescends C := by
  intro X Y sX _ sY _ p _ hp k
  exact properPushforwardFactorsThroughRationalEquivalence C sX sY p hp k

end Stacks.Chow

end
