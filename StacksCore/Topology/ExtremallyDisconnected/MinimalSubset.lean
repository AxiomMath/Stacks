module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# Minimal quasi-compact subsets surjecting onto a quasi-compact Hausdorff space

Stacks 08YM: a continuous surjection `f : X → Y` of quasi-compact Hausdorff spaces admits a
quasi-compact `E ⊆ X` with `f '' E = Y` such that no proper closed subset of `E` surjects onto
`Y`.

This is Mathlib's lemma, stated there for a continuous surjection out of a quasi-compact space
onto a Fréchet (T₁) space, hence in greater generality, and quantifying the minimality clause
over the closed subsets of `E` in its subspace topology.

## References

* [Stacks Project, Tag 08YM](https://stacks.math.columbia.edu/tag/08YM)
-/

@[expose] public section

add_to_stacks 08YM "a minimal quasi-compact subset that still surjects"
  exists_compact_surjective_zorn_subset
