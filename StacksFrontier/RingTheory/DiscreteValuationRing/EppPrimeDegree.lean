module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.FiniteSupportAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.ReducedFactorPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.MixedFiniteLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.WildCharP
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.MixedWildAssembly

/-!
# The prime-degree input to Epp's theorem

This file assembles the equal- and mixed-characteristic prime-degree solvers consumed by
`Stacks.EppTheorem.FamilyPrimeDegreeSolvable`.  The first construction below packages the finite
weakly-unramified residue absorption with its fraction field.  Keeping the ring and field in one
existential is essential: the corrected all-conjugates bridge uses the ring as its valuation base
and the field as the finite scalar extension.
-/
