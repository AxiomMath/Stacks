module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksCore.Tactic.StacksAttribute

/-!
# A limit as the equalizer of two maps between products

For a diagram `F : J ⥤ C`, write `I` for the objects and `A` for the arrows of `J`. Given a
limiting fan on `∏_{i ∈ I} F i`, a limiting fan on `∏_{a ∈ A} F (t a)`, and a limiting fork for
the two maps `φ ψ` between them determined by `p_a ∘ ψ = F a ∘ p_{s a}` and `p_a ∘ φ = p_{t a}`,
the equalizer is a limit of `F`, with legs the equalizer map followed by the projections.
Mathlib's `HasLimitOfHasProductsOfHasEqualizers.buildIsLimit` states exactly this, assuming only
that these two products and this one equalizer exist (as limiting cones), which is Stacks' Lemma
002N.

Stacks' tag is also attached, in `StacksCore/CategoryTheory/Limits.lean`, to Mathlib's
`limitConeOfEqualizerAndProduct`, the variant which assumes that `C` has all equalizers.

## References

* [Stacks Project, Tag 002N](https://stacks.math.columbia.edu/tag/002N)
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 002N "the equalizer of the two maps between the products is the limit, assuming \
  just the two products and the one equalizer exist"
  HasLimitOfHasProductsOfHasEqualizers.buildIsLimit
