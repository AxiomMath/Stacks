module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence

/-!
# Flat pullback descends to Chow groups: the bundled hypothesis, discharged

`Stacks.Chow.FlatPullbackDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction` bundles Stacks 02S1 over
all of its inputs: it asserts that for every pair of schemes locally of finite type over the base,
every morphism between them over the base which is flat and locally of finite type of relative
dimension `r`, and every degree, flat pullback of cycles carries cycles rationally equivalent to
zero to cycles rationally equivalent to zero. Being a `Pi` into `Prop` it is itself a `Prop`, and
the bivariant development takes it as a hypothesis in that bundled shape because a bivariant class
caps with test morphisms that are produced inside the construction, so the morphisms Stacks 02S1 is
needed for are not available to be named in advance.

The hypothesis is not open. Stacks 02S1 is proved in this repository for an arbitrary flat
morphism of relative dimension `r` over the base, as
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`, and so the bundled
form is a theorem: that is `Stacks.Chow.flatPullbackDescends` below. It is the exact analogue of
`Stacks.Chow.properPushforwardDescends`, which discharges the companion hypothesis
`Stacks.Chow.ProperPushforwardDescends` for Stacks 02S2.

This file exists only to join the two. `Stacks.Chow.FlatPullbackDescends` is stated upstream of
its proof: the module stating it has an import closure of 551 modules and 35 dependents, and the
proof needs 147 modules that closure does not contain, so discharging it where it is stated would
push those modules into every one of those dependents. Proving it in a downstream leaf instead
costs nothing to anybody: a consumer that wants the theorem rather than the hypothesis imports
this module, and a consumer that does not is unaffected.

## Main results

* `Stacks.Chow.flatPullbackDescends` — `Stacks.Chow.FlatPullbackDescends` holds for every
  `Stacks.Chow.ChowSituation`.

## Implementation notes

No `@[stacks 02S1]` attribute is attached. Stacks 02S1 is already carried in its general form by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and in the open immersion
cases by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι` and
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion`; the statement
below adds no mathematical content to the first of those, it only quantifies over the inputs it is
already universally quantified over, so tagging it would double-count the tag rather than extend
its coverage. This is the same judgement recorded in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent` for
Stacks 02S2.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 02S1, bundled over all of its inputs.** For every base situation, flat pullback of
cycles along every morphism over the base which is flat and locally of finite type of relative
dimension `r`, in every degree, carries cycles rationally equivalent to zero to cycles rationally
equivalent to zero.

This is `Stacks.Chow.FlatPullbackDescends`, the hypothesis the bivariant development of
Stacks 0FDZ carries, proved outright. A consumer that can reach this module should supply it
instead of assuming it. -/
theorem flatPullbackDescends (C : ChowSituation.{u}) : FlatPullbackDescends C := by
  intro A B sA _ sB _ v _ _ hv r hr k
  exact flatPullbackFactorsThroughRationalEquivalence_general C sA sB v hv r hr k

end Stacks.Chow

end
