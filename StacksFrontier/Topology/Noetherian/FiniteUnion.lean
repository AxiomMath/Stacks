module

public import Mathlib.Topology.NoetherianSpace
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite unions of Noetherian subspaces

Stacks 0053: a finite union of Noetherian subspaces of a topological space is Noetherian in the
induced topology. This is Mathlib's theorem, which takes the Noetherianness of the pieces as
instances rather than as an explicit hypothesis.
-/

@[expose] public section

-- The former @[stacks 0053, ega] theorem is the Mathlib theorem.
add_to_stacks 0053 TopologicalSpace.NoetherianSpace.iUnion
add_to_ega "0 2.2.3" "converse"
  TopologicalSpace.NoetherianSpace.iUnion
