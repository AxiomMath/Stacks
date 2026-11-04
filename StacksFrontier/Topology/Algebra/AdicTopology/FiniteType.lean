module

public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.RestrictedPowerSeries
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.WeakIdealConditions
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.Equivalences
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.IdealOfDefinition

/-!
# Algebras topologically of finite type

A topological `A`-algebra `B` is *topologically of finite type* when it is a quotient of a ring
of restricted power series over `A`.  The notion, the ring of restricted power series and the
conditions are in `FiniteType.RestrictedPowerSeries`; the implications between the conditions
that do not construct a presentation are in `FiniteType.WeakIdealConditions`; the equivalence of
the four standard characterisations is in `FiniteType.Equivalences`; and the characterisation
modulo an ideal of definition (Stacks 0CB6) is in `FiniteType.IdealOfDefinition`.
-/
