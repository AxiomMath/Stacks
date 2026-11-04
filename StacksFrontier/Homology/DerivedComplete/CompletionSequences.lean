module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.SequenceData
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.KoszulTowerComparison
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.ModuleCohomology
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.TruncationSequences

/-!
# Cohomology of derived completion at a principal ideal

This file re-exports its four parts in `CompletionSequences/`:
`SequenceData`, `KoszulTowerComparison`, `ModuleCohomology` and `TruncationSequences`.

For an element `f` of a commutative ring, the derived completion of a module has cohomology only
in degrees `-1` and `0`. Its degree `-1` cohomology is the `f`-adic Tate module, while degree zero
lies in the short exact sequence involving the first derived inverse limit of the `f`-power
torsion and the ordinary `f`-adic completion. For an arbitrary derived object this gives a short
exact sequence relating completion and cohomology.

## Main definitions

* `CompletionSequences.powerMultiplication`: multiplication by a power of an element on a module.
* `CompletionSequences.powerTorsionSystem`: the inverse system of `f`-power torsion submodules.
* `CompletionSequences.powerQuotientSystem`: the inverse system of quotients by powers of `f`.
* `CompletionSequences.adicTateModule`: the inverse limit of the power-torsion system.
* `CompletionSequences.principalCompletionUnit`: the actual map into the fixed mapping-cocone
  model.
* `CompletionSequences.PrincipalCompletionSequences`: the two sequences and their normalized maps.

## Main results

* `CompletionSequences.derivedCompletion_principal_homology`: the cohomology calculations and
  short exact sequences for derived completion at `(f)`.

## Implementation notes

Positive powers are indexed by `n : ℕ` as `f ^ (n + 1)`. Derived completion is represented by
an arbitrary left adjoint to the inclusion of the full subcategory of derived-complete objects.
The derived limit is the image of the mapping cocone of `1 - shift` on the product of
complexes. Its comparison with completion is normalized by the actual chain-level unit.
The `R¹ lim` terms have both a cokernel model and a degree-one derived-limit model, with
comparison isomorphisms normalized by the connecting morphism. The two arrows in the module
sequence are uniquely specified by `connecting_inclusion` and `projection_π`. The arrows
for a derived object are composites of the completed canonical truncation maps, with
endpoint comparisons normalized on homology and with respect to the completion unit.

## References

* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
-/
