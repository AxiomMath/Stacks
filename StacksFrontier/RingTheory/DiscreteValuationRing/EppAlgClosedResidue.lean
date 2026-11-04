module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.SolvableInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TameCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TotallyRamifiedTensor
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.FiniteLevelCyclotomic
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IntermediateFieldInduction

/-!
# Eliminating ramification over a complete discrete valuation ring

Let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction fields
`K ⊆ L ⊆ M`. Suppose that the residue field of `A` is algebraically closed of
positive characteristic `p`, that `A` and `B` are complete, that `A → B` is weakly
unramified, that `M / L` is finite, and that the image of the residue field of `A` in
the residue field of `B` is the intersection of all sets of `p ^ n`-th powers. Then
ramification in `A → C` can be eliminated after a finite extension of `K`.

## Main results

* `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution` gives a finite extension
  of `K` which is a weak solution for `A → C`.

## Implementation notes

Completeness is maximal-ideal-adic completeness. The residue-field intersection is
expressed elementwise in the residue field of `B`. The weak solution includes the
canonical reduced compositum and integral closures, packaged by
`IsDiscreteValuationRing.IntegralClosureBaseChange`.

The reduction of a commutative ring by its nilradical, and the equivalence of reductions
induced by an algebra equivalence, are set up here as auxiliary constructions.

## References

* [The Stacks Project, Tag 09F8](https://stacks.math.columbia.edu/tag/09F8)
* [Epp]
-/

