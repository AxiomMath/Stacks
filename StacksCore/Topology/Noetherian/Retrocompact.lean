module

public import Mathlib.Topology.Constructible
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compactness and retrocompactness in a Noetherian space

## Main results

* `TopologicalSpace.NoetherianSpace.compactSpace` (Stacks 04ZA, part 1) is registered
  directly from Mathlib: a Noetherian space is quasi-compact.
* `noetherianSpace_isRetrocompact` (Stacks 04ZA, part 2): every subset of a Noetherian space is
  retrocompact.

## References

* [Stacks Project, Tag 04ZA](https://stacks.math.columbia.edu/tag/04ZA)
-/

@[expose] public section

add_to_stacks 04ZA "(1)" TopologicalSpace.NoetherianSpace.compactSpace
add_to_ega "0 2.2.4" "first assertion" TopologicalSpace.NoetherianSpace.compactSpace

/-- **Stacks 04ZA** (part 2). Every subset of a Noetherian topological space is retrocompact:
its intersection with any quasi-compact open is quasi-compact. -/
@[stacks 04ZA "part (2)"]
theorem noetherianSpace_isRetrocompact (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (E : Set X) : IsRetrocompact E :=
  fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _
