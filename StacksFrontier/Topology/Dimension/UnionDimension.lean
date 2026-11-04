module

public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The dimension of a union of closed subsets

On a quasi-sober space the dimension of a union of two closed subsets is at most the larger of
the two dimensions: the closure of a point of the union lies inside one of the two pieces, and on
a quasi-sober space the dimension of a closed subset is controlled by the dimensions of the
closures of its points.

## Main results

* `topologicalKrullDim_union_le` — `dim (A ∪ B) ≤ max (dim A) (dim B)` for closed `A`, `B`.
* `topologicalKrullDim_le_max_of_subset_union` — the same for a closed subset of such a union,
  with the two pieces cut down to it.
* `topologicalKrullDim_inter_le_max_of_subset_union` — if `T ∩ W ⊆ Z ∪ E` then
  `dim (T ∩ W) ≤ max (dim (T ∩ Z)) (dim E)`, the form used in the proof of Stacks 0B0E.
* `topologicalKrullDim_le_of_subset_biUnion` and `topologicalKrullDim_biUnion_le` — the same for
  a finite family of pieces.
-/

@[expose] public section

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **The dimension of a union of two closed subsets is at most the larger of the two
dimensions.** The closure of a point of the union lies in whichever piece contains the point. -/
public theorem topologicalKrullDim_union_le [QuasiSober X] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) :
    topologicalKrullDim ↥(A ∪ B) ≤
      max (topologicalKrullDim ↥A) (topologicalKrullDim ↥B) := by
  refine topologicalKrullDim_le_of_forall_closure (hA.union hB) fun x hx => ?_
  rcases hx with h | h
  · exact le_trans (topologicalKrullDim_le_of_subset
      (closure_minimal (Set.singleton_subset_iff.mpr h) hA)) (le_max_left _ _)
  · exact le_trans (topologicalKrullDim_le_of_subset
      (closure_minimal (Set.singleton_subset_iff.mpr h) hB)) (le_max_right _ _)

/-- The closure of a point lying in two closed sets `S` and `C` has dimension at most that of
`S ∩ C`. -/
private theorem topologicalKrullDim_closure_singleton_le_inter {S C : Set X} {x : X}
    (hS : IsClosed S) (hC : IsClosed C) (hxS : x ∈ S) (hxC : x ∈ C) :
    topologicalKrullDim ↥(closure ({x} : Set X)) ≤ topologicalKrullDim ↥(S ∩ C) :=
  topologicalKrullDim_le_of_subset (Set.subset_inter
    (closure_minimal (Set.singleton_subset_iff.mpr hxS) hS)
    (closure_minimal (Set.singleton_subset_iff.mpr hxC) hC))

/-- **A closed subset of a union of two closed subsets.** Its dimension is at most the larger of
the dimensions of its two intersections with the pieces. -/
public theorem topologicalKrullDim_le_max_of_subset_union [QuasiSober X] {S A B : Set X}
    (hS : IsClosed S) (hA : IsClosed A) (hB : IsClosed B) (hSAB : S ⊆ A ∪ B) :
    topologicalKrullDim ↥S ≤
      max (topologicalKrullDim ↥(S ∩ A)) (topologicalKrullDim ↥(S ∩ B)) := by
  refine topologicalKrullDim_le_of_forall_closure hS fun x hx => ?_
  rcases hSAB hx with h | h
  · exact (topologicalKrullDim_closure_singleton_le_inter hS hA hx h).trans (le_max_left _ _)
  · exact (topologicalKrullDim_closure_singleton_le_inter hS hB hx h).trans (le_max_right _ _)

/-- If the closed subset `T ∩ W` lies inside `Z ∪ E` with `Z` and `E` closed, then
`dim (T ∩ W) ≤ max (dim (T ∩ Z)) (dim E)`. -/
public theorem topologicalKrullDim_inter_le_max_of_subset_union [QuasiSober X]
    {T W Z E : Set X} (hT : IsClosed T) (hW : IsClosed W) (hZ : IsClosed Z) (hE : IsClosed E)
    (h : T ∩ W ⊆ Z ∪ E) :
    topologicalKrullDim ↥(T ∩ W) ≤
      max (topologicalKrullDim ↥(T ∩ Z)) (topologicalKrullDim ↥E) := by
  refine le_trans (topologicalKrullDim_le_max_of_subset_union (hT.inter hW) hZ hE h) ?_
  refine max_le_max (topologicalKrullDim_le_of_subset ?_) (topologicalKrullDim_le_of_subset ?_)
  · exact fun y hy => ⟨hy.1.1, hy.2⟩
  · exact fun y hy => hy.2

/-- **A closed subset of a finite union of closed subsets.** If the closed set `S` lies inside
the union of a `Finset`-indexed family of closed sets and each piece cuts out of `S` a subset of
dimension at most `c`, then `dim S ≤ c`. -/
public theorem topologicalKrullDim_le_of_subset_biUnion [QuasiSober X] {ι : Type*}
    (t : Finset ι) {S : Set X} {A : ι → Set X} (hS : IsClosed S) (hA : ∀ i, IsClosed (A i))
    (hSA : S ⊆ ⋃ i ∈ t, A i) {c : WithBot ℕ∞}
    (hc : ∀ i ∈ t, topologicalKrullDim ↥(S ∩ A i) ≤ c) :
    topologicalKrullDim ↥S ≤ c := by
  refine topologicalKrullDim_le_of_forall_closure hS fun x hx => ?_
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (hSA hx)
  exact (topologicalKrullDim_closure_singleton_le_inter hS (hA i) hx hxi).trans (hc i hit)

/-- **The dimension of a finite union of closed subsets** is at most any bound shared by the
pieces. -/
public theorem topologicalKrullDim_biUnion_le [QuasiSober X] {ι : Type*} (t : Finset ι)
    {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) {c : WithBot ℕ∞}
    (hc : ∀ i ∈ t, topologicalKrullDim ↥(A i) ≤ c) :
    topologicalKrullDim ↥(⋃ i ∈ t, A i) ≤ c := by
  refine topologicalKrullDim_le_of_subset_biUnion t
    (t.finite_toSet.isClosed_biUnion fun i _ => hA i) hA Set.Subset.rfl fun i hi => ?_
  exact le_trans (topologicalKrullDim_le_of_subset Set.inter_subset_right) (hc i hi)

end
