module

public import Mathlib.Topology.Compactness.Compact
import StacksCore.Tactic.StacksAttribute

/-!
# Tychonoff's theorem for quasi-compact spaces

An arbitrary product of quasi-compact spaces is quasi-compact. This is registered directly
as Mathlib's `Pi.compactSpace` instance.

Quasi-compactness is expressed by `CompactSpace`; no Hausdorff assumption is imposed on the
factors or on their product.

## References

* [Stacks Project, Tag 08ZU](https://stacks.math.columbia.edu/tag/08ZU)
-/

@[expose] public section

add_to_stacks 08ZU "Tychonoff's theorem: a product of quasi-compact spaces is quasi-compact"
  Pi.compactSpace
