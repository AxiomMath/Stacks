module

public import Mathlib.Basic.Rel
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The graph of a continuous map to a Hausdorff space

## Main results

* `Continuous.isClosed_graph` (Stacks 08ZF): the graph of a continuous map into a Hausdorff
  space is closed in the product.
-/

@[expose] public section

/-- **Stacks 08ZF.** The graph of a continuous map `f : X → Y` into a Hausdorff space is a
closed subset of `X × Y`: it is the equaliser of `f ∘ Prod.fst` and `Prod.snd`. -/
@[stacks 08ZF]
theorem Continuous.isClosed_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : Continuous f) : IsClosed (Function.graph f) :=
  isClosed_eq (hf.comp continuous_fst) continuous_snd
