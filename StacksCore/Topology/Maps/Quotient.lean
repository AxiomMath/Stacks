module

public import Mathlib.Topology.Order
import StacksCore.Tactic.StacksAttribute

/-!
# Quotient topologies

For a topology `t` on `X` and a map `f : X → Y`, the quotient topology `t.coinduced f` makes
`f` continuous and is the strongest topology doing so. In Mathlib's order on topologies,
this means it is the least such topology.

Its open and closed subsets are exactly the subsets whose preimages are open and closed,
respectively. All three parts are registered directly from Mathlib.

## References

* [Stacks Project, Tag 08ZK](https://stacks.math.columbia.edu/tag/08ZK)
-/

@[expose] public section

add_to_stacks 08ZK "f is continuous for the quotient topology" continuous_coinduced_rng
add_to_stacks 08ZK "the quotient topology is the strongest one making f continuous"
  continuous_iff_coinduced_le
add_to_stacks 08ZK "(2) the opens of the quotient topology" isOpen_coinduced
add_to_stacks 08ZK "(3) the closed sets of the quotient topology" isClosed_coinduced
