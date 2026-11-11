module

public import StacksFrontier.Topology.Profinite.Characterization
public import StacksFrontier.Topology.Profinite.Defs

/-!
# Profinite spaces in the sense of the Stacks Project

A space is profinite in the sense of Stacks 08ZX (`IsProfiniteStacks`: homeomorphic to the limit of
an arbitrary diagram of finite discrete spaces) iff it is Hausdorff, quasi-compact and totally
disconnected, and such a space is a cofiltered limit of finite discrete spaces (`IsProfinite`).

## Main results

* `isProfiniteStacks_iff_t2_compact_totallyDisconnected_and_isProfinite` (Stacks 08ZY).
-/

@[expose] public section

universe u

/-- **Stacks 08ZY.** For a topological space `X` the following are equivalent: (1) `X` is a
profinite space, i.e. homeomorphic to the limit of a diagram of finite discrete spaces (Stacks
08ZX, `IsProfiniteStacks`); (2) `X` is Hausdorff, quasi-compact and totally disconnected. If this
is true, then `X` is a cofiltered limit of finite discrete spaces (`IsProfinite`). -/
@[stacks 08ZY "Both directions and the final sentence. Profinite is `IsProfiniteStacks` (Stacks \
08ZX): homeomorphic to the limit of an arbitrary diagram of finite discrete spaces indexed by a \
small category in the universe of `X`; the cofiltered conclusion is `IsProfinite`."]
theorem isProfiniteStacks_iff_t2_compact_totallyDisconnected_and_isProfinite
    (X : Type u) [TopologicalSpace X] :
    (IsProfiniteStacks X ↔ T2Space X ∧ CompactSpace X ∧ TotallyDisconnectedSpace X) ∧
      (IsProfiniteStacks X → IsProfinite X) := by
  have h := isProfiniteStacks_iff_compact_t2_totallyDisconnected X
  refine ⟨⟨fun hX => ?_, fun ⟨_, _, _⟩ => h.2 ⟨inferInstance, inferInstance, inferInstance⟩⟩,
    fun hX => ?_⟩
  · obtain ⟨_, _, _⟩ := h.1 hX
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨_, _, _⟩ := h.1 hX
    exact isProfinite_of_t2_compact_totallyDisconnected X
