module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShortExactSequences
public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShiftCompatibility
public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.BoundaryMaps
public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ComparisonDiagram

/-!
# Comparison of ordinary and derived completion at a principal ideal

This file collects the parts `CompletionSequencesComparison/ShortExactSequences`,
`CompletionSequencesComparison/ShiftCompatibility`, `CompletionSequencesComparison/BoundaryMaps`
and `CompletionSequencesComparison/ComparisonDiagram`.

Let `f` be an element of a commutative ring `A` and let `K` be an object of `D(A)`. The ordinary
`f`-adic completion of `Hᵖ(K)`, the cohomology of the derived completion of `Hᵖ(K)`, the
cohomology of the derived completion of `K`, and the inverse limits of the cohomology of the
tensor products `K ⊗ᴸ_A (A →[f^n] A)` fit into a commutative diagram of four short exact
sequences whose bottom comparison is an isomorphism of first derived inverse limits.

## Main definitions

* `PrincipalCompletionDiagram.principalKoszulSystem`: the inverse system of two-term complexes
  `(A →[f^(n+1)] A)` in the derived category.

## Main results

* `PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison`: the commutative
  diagram of four short exact sequences comparing ordinary and derived completion at `(f)`.

## Implementation notes

The comparison is made at the level of the inverse systems: the termwise cone sequences
`Hᵖ(K)/fⁿ → Hᵖ(K ⊗ᴸ (A →[fⁿ] A)) → Hᵖ⁺¹(K)[fⁿ]` are assembled with the Mittag-Leffler condition
for the quotient system, the Milnor triangle of the fixed mapping-cocone model supplies the
middle column, and the bottom isomorphism is the cokernel comparison of the two presentations of
`R¹lim`. Each of the three commuting squares is proved as a separate lemma over abstract
completion data, after the appropriate limit projection, kernel inclusion or cokernel
epimorphism.

## References

* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
-/
