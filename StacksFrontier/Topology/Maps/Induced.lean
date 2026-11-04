module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Order

import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of the induced topology

Stacks 09R8: for a topological space `X`, a set `Y` and a map `f : Y → X`, the induced topology
`TopologicalSpace.induced f tX` on `Y` is characterized by each of (1) it is the weakest topology
making `f` continuous, (2) its opens are exactly the preimages of opens of `X`, and (3) its closed
sets are exactly the preimages of closed sets of `X`.

All three are Mathlib theorems. In Mathlib's order on `TopologicalSpace Y`, `s ≤ t` means `s` is
*finer* than `t`, so the weakest (coarsest) topology of (1) is the `≤`-largest element, and
`continuous_iff_le_induced` says exactly that a topology on `Y` makes `f` continuous iff it is
`≤ induced f tX`. The injectivity hypothesis of the tag is not needed: all three hold for
arbitrary `f`.

Since the closed sets of the induced topology are the preimages of closed sets, the image of a
closed set under an inducing map is closed in the range. It is therefore closed outright as soon
as it is contained in a closed set which the range contains, which is
`Topology.IsInducing.isClosed_image_of_subset_of_subset_range`.
-/

@[expose] public section

-- The former @[stacks 09R8] theorems are the Mathlib theorems.
add_to_stacks 09R8 "(1) the induced topology is the weakest one making the map continuous"
  continuous_iff_le_induced
add_to_stacks 09R8 "(2) the opens are the preimages of opens" isOpen_induced_iff
add_to_stacks 09R8 "(3) the closed sets are the preimages of closed sets" isClosed_induced_iff

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- The image of a closed set under an inducing map is closed, provided it is contained in a
closed set which is itself contained in the range: the image is closed in the range, and
intersecting the witnessing closed set of `Y` with the sandwiching one removes the range. -/
theorem isClosed_image_of_subset_of_subset_range (hf : IsInducing f) {s : Set X}
    (hs : IsClosed s) {C : Set Y} (hC : IsClosed C) (hsC : f '' s ⊆ C)
    (hCf : C ⊆ Set.range f) : IsClosed (f '' s) := by
  obtain ⟨t, ht, hts⟩ := hf.image_eq_isClosed_inter_range hs
  have heq : f '' s = t ∩ C := by
    refine Set.Subset.antisymm (fun b hb => ⟨(hts ▸ hb).1, hsC hb⟩) fun b hb => ?_
    rw [hts]
    exact ⟨hb.1, hCf hb.2⟩
  rw [heq]
  exact ht.inter hC

end Topology.IsInducing
