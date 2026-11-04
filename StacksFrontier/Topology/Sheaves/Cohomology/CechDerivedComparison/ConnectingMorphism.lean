module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism.ExtendedHomologyDelta
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism.MappingConePlusDelta
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism.DerivedDeltaEq

/-!
# The `derivedδ_eq` field of the Čech-to-derived comparison of Stacks 01EN

This module re-exports its three parts: `ConnectingMorphism.ExtendedHomologyDelta` (the
connecting morphism of the extension by zero of a short exact sequence of `ℕ`-indexed complexes,
conjugated by `extendedHomologyIso`), `ConnectingMorphism.MappingConePlusDelta` (the mapping cone
of the extended sequence in `K⁺`, and the compatibility of its connecting morphism with `RF`), and
`ConnectingMorphism.DerivedDeltaEq` (the commuting square `comm₃_resolutionDerivedComparison`, its
Čech instance `comm₃_cech`, and the field `Stacks.Cohomology.CechComparison.derivedδ_eq`).
-/
