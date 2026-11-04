module

public import Mathlib.Topology.Homeomorph.Lemmas
import StacksCore.Tactic.StacksAttribute

/-!
# Continuous bijections from quasi-compact spaces to Hausdorff spaces

A continuous bijection from a quasi-compact space to a Hausdorff space is a homeomorphism.
Mathlib's `isHomeomorph_iff_continuous_bijective` is registered directly: it states the result
as an equivalence, so the Stacks conclusion is its reverse implication.

## References

* [Stacks Project, Tag 08YE](https://stacks.math.columbia.edu/tag/08YE)
-/

@[expose] public section

add_to_stacks 08YE "a continuous bijection out of a quasi-compact space is a homeomorphism"
  isHomeomorph_iff_continuous_bijective
