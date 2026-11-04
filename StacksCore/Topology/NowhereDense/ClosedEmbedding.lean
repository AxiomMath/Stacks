module

public import Mathlib.Topology.GDelta.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Images of nowhere dense subsets under closed embeddings

A closed embedding carries nowhere dense subsets to nowhere dense subsets.
Mathlib's `Topology.IsInducing.isNowhereDense_image` proves this for any inducing map,
so it applies in particular to closed embeddings.

## References

* [Stacks Project, Tag 03HQ](https://stacks.math.columbia.edu/tag/03HQ)
-/

@[expose] public section

add_to_stacks 03HQ "for an inducing map"
  Topology.IsInducing.isNowhereDense_image
