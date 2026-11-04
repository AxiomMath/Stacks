module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Proper.ClosedProjection

/-!
# Quasi-compactness via closed projections

A topological space `X` is quasi-compact exactly when the projection `Z × X → Z` is a closed
map for every topological space `Z`. No separation hypothesis is imposed on any of the spaces
involved.

## Main results

* `compactSpace_iff_isClosedMap_fst`: quasi-compactness of `X` is equivalent to closedness of
  the projection `Prod.fst : Z × X → Z` for every `Z`.
-/

@[expose] public section

/-- **Stacks 005Q**.
A topological space `X` is quasi-compact (`CompactSpace X`) if and only if, for every
topological space `Z`, the first projection `Prod.fst : Z × X → Z` is a closed map. -/
@[stacks 005Q]
theorem compactSpace_iff_isClosedMap_fst (X : Type) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ (Z : Type) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z) :=
  compactSpace_iff_forall_isClosedMap_fst X
