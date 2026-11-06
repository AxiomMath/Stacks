module

public import Mathlib.Basic.Rel
public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# The graph of a continuous map to a Hausdorff space

## Main results

* `Continuous.isClosed_graph` (Stacks 08ZF): the graph of a continuous map into a Hausdorff
  space is closed in the product.
-/

@[expose] public section

/-! `Continuous.isClosed_graph` is now in Mathlib (`Mathlib.Topology.Separation.Hausdorff`);
we only attach the Stacks tag here. -/
add_to_stacks 08ZF Continuous.isClosed_graph
