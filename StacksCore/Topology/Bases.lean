module

public import Mathlib.Topology.Bases
import StacksCore.Tactic.StacksAttribute

/-! # Bases -/

@[expose] public section

add_to_stacks 004P TopologicalSpace.IsTopologicalBasis
add_to_stacks 004P TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
add_to_stacks 004P TopologicalSpace.IsTopologicalBasis.isOpen_iff

add_to_stacks 08ZI TopologicalSpace.generateFrom
add_to_stacks 08ZI TopologicalSpace.isTopologicalBasis_of_subbasis
