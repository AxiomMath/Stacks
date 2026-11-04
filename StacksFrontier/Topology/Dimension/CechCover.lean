module

public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# A two-layer cover of a Noetherian space of dimension at most one

Let `X` be a Noetherian sober `T0` space with `topologicalKrullDim X ≤ 1` and let `W` be an
open cover of `X`. The refinement result
`Stacks.Topology.Dimension.exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one`
refines `W` to a *pairwise disjoint* family `A`, one open per irreducible component, each inside
a member of `W`, whose union `G` has finite complement `T` consisting of closed points. This
file completes that to an honest open cover of `X` by adjoining one open `V x` per point
`x ∈ T`, again subordinate to `W`, chosen so that `V x` isolates `x` inside `T`:

* `V x ∩ T = {x}`, hence
* `G ∩ V x = V x \ {x}`, and
* `V x ∩ V y ⊆ G` whenever `x ≠ y`, and
* `V x \ {x} = ⋃ C, A C ∩ V x`, a *pairwise disjoint* decomposition into opens each contained
  in a single irreducible component.

The last two identities are what make this cover useful. Every pairwise intersection of two
distinct members other than `G ∩ V x` lies inside `G`, so for a cover of this shape any
alternating family of transition data on the overlaps with `G` extends to the remaining
overlaps by the ratios of those data, and the resulting family satisfies every cocycle
condition *identically* — all triple intersections of distinct members are contained in `G`,
where every datum has already been written in terms of the data on `G ∩ V x`. In the
one-dimensional lifting problems of the Stacks project — `Pic(X) → Pic(Z)` for a closed
immersion `Z → X`, [Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) — this
removes the degree-two obstruction without any vanishing theorem, and leaves exactly the
degree-one problem of extending finitely many sections across the punctured opens
`V x \ {x} = G ∩ V x` — and that problem splits, by the last identity, into one independent
problem per irreducible component, over an open set contained in a single component.

## Main results

* `Stacks.Topology.Dimension.exists_isolating_opens`: around a finite set `T` of closed points
  of any topological space, and subordinate to any open cover, there are opens `V x` for
  `x ∈ T` with `V x ∩ T = {x}`. No dimension, Noetherian or separation hypothesis.
* `Stacks.Topology.Dimension.exists_isolating_cover_of_topologicalKrullDim_le_one`: the
  two-layer cover described above, for a Noetherian sober `T0` space of Krull dimension at
  most one, with the decomposition of each punctured overlap into its component pieces.

## Implementation notes

`V x` is simply `W (jV x) ∩ (T \ {x})ᶜ` for a member `W (jV x)` of the cover containing `x`:
the set `T \ {x}` is a finite set of closed points, hence closed, so its complement is open.
Nothing else is used, which is why `exists_isolating_opens` needs no hypothesis on the space.

The finite set `T` is not given a name in the statement of the second theorem; it appears as
`(⋃ C, A C)ᶜ`, the complement of the union of the disjoint family, so that no extra
existential has to be introduced and the identities read directly against the data they
constrain.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

open Set TopologicalSpace Topology

universe u

namespace Stacks.Topology.Dimension

variable {X : Type u} [TopologicalSpace X]

/-- A finite set of closed points is closed. -/
theorem isClosed_of_finite_of_forall_isClosed_singleton {T : Set X} (hTf : T.Finite)
    (hTc : ∀ x ∈ T, IsClosed ({x} : Set X)) : IsClosed T := by
  rw [← Set.biUnion_of_singleton T]
  exact hTf.isClosed_biUnion hTc

/-- **Isolating opens around a finite set of closed points.** Let `T` be a finite set of closed
points of a topological space and let `W` be an open cover. Then there are open sets `V x`,
one for each `x ∈ T`, with `x ∈ V x`, each contained in a member of the cover, and each meeting
`T` in `x` alone.

No hypothesis on the space is needed: `V x` is cut out of a member of the cover by removing the
closed set `T \ {x}`. -/
theorem exists_isolating_opens {T : Set X} (hTf : T.Finite)
    (hTc : ∀ x ∈ T, IsClosed ({x} : Set X))
    {ι : Type*} {W : ι → Set X} (hWo : ∀ i, IsOpen (W i)) (hWc : ∀ x : X, ∃ i, x ∈ W i) :
    ∃ (V : X → Set X) (jV : X → ι), ∀ x ∈ T,
      IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ W (jV x) ∧ V x ∩ T = {x} := by
  choose jV hjV using hWc
  refine ⟨fun x => W (jV x) ∩ (T \ {x})ᶜ, jV, fun x hx => ⟨?_, ?_, inter_subset_left, ?_⟩⟩
  · exact (hWo _).inter
      (isClosed_of_finite_of_forall_isClosed_singleton (hTf.subset sdiff_subset)
        (fun y hy => hTc y hy.1)).isOpen_compl
  · exact ⟨hjV x, fun h => h.2 rfl⟩
  · refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 ⟨⟨hjV x, fun h => h.2 rfl⟩, hx⟩)
    by_contra hne
    exact hy.1.2 ⟨hy.2, hne⟩

/-- **The two-layer cover of a Noetherian space of dimension at most one.** Given an open cover
`W` of a Noetherian sober `T0` space of Krull dimension at most one, there is a pairwise
disjoint family `A`, one open per irreducible component and each inside a member of `W`,
together with one further open `V x` inside a member of `W` for each point `x` of the finite
complement `T` of `G = ⋃ C, A C`, such that

* the `A C` together with the `V x` cover `X`;
* `V x` meets `T` in `x` alone, equivalently `G ∩ V x = V x \ {x}`;
* `V x ∩ V y ⊆ G` for `x ≠ y`;
* `V x \ {x} = ⋃ C, A C ∩ V x`, the pieces being pairwise disjoint and each contained in a
  single irreducible component.

So apart from the overlaps `G ∩ V x` — punctured neighbourhoods of the finitely many points of
`T` — every intersection of distinct members of this cover is contained in `G`, and each of
those punctured overlaps breaks up into one piece per irreducible component. -/
theorem exists_isolating_cover_of_topologicalKrullDim_le_one [T0Space X] [NoetherianSpace X]
    [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1)
    {ι : Type*} {W : ι → Set X} (hWo : ∀ i, IsOpen (W i)) (hWc : ∀ x : X, ∃ i, x ∈ W i) :
    ∃ (A : irreducibleComponents X → Set X) (jA : irreducibleComponents X → ι)
      (V : X → Set X) (jV : X → ι),
      (∀ C, IsOpen (A C)) ∧ (∀ C, A C ⊆ W (jA C)) ∧
        (∀ C, closure (A C) = (C : Set X)) ∧
        Pairwise (Function.onFun Disjoint A) ∧
        ((⋃ C, A C)ᶜ).Finite ∧
        (∀ x ∈ (⋃ C, A C)ᶜ, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ W (jV x) ∧
          V x ∩ (⋃ C, A C)ᶜ = {x} ∧ (⋃ C, A C) ∩ V x = V x \ {x}) ∧
        (∀ x ∈ (⋃ C, A C)ᶜ, ∀ y ∈ (⋃ C, A C)ᶜ, x ≠ y → V x ∩ V y ⊆ ⋃ C, A C) ∧
        ((⋃ C, A C) ∪ ⋃ x ∈ (⋃ C, A C)ᶜ, V x) = univ ∧
        (∀ x ∈ (⋃ C, A C)ᶜ, V x \ {x} = ⋃ C, A C ∩ V x) := by
  obtain ⟨A, jA, hAo, hAW, hAcl, hAdisj, hfin, hTcl⟩ :=
    exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one hdim hWo hWc
  obtain ⟨V, jV, hV⟩ := exists_isolating_opens hfin hTcl hWo hWc
  have eq_of_mem_of_notMem : ∀ x ∈ (⋃ C, A C)ᶜ, ∀ z ∈ V x, z ∉ ⋃ C, A C → z = x :=
    fun x hx z hz hzG => by
      rw [← mem_singleton_iff, ← (hV x hx).2.2.2]
      exact ⟨hz, hzG⟩
  have key : ∀ x ∈ (⋃ C, A C)ᶜ, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ W (jV x) ∧
      V x ∩ (⋃ C, A C)ᶜ = {x} ∧ (⋃ C, A C) ∩ V x = V x \ {x} := by
    intro x hx
    obtain ⟨hVo, hxV, hVW, hVT⟩ := hV x hx
    refine ⟨hVo, hxV, hVW, hVT, Subset.antisymm ?_ ?_⟩
    · intro z hz
      refine ⟨hz.2, fun hzx => ?_⟩
      have hzx' : z = x := hzx
      exact hx (hzx' ▸ hz.1)
    · intro z hz
      refine ⟨?_, hz.1⟩
      by_contra hzG
      exact hz.2 (eq_of_mem_of_notMem x hx z hz.1 hzG)
  refine ⟨A, jA, V, jV, hAo, hAW, hAcl, hAdisj, hfin, key, fun x hx y hy hxy => ?_, ?_,
    fun x hx => by rw [← (key x hx).2.2.2.2]; exact Set.iUnion_inter _ _⟩
  · intro z hz
    by_contra hzG
    exact hxy ((eq_of_mem_of_notMem x hx z hz.1 hzG).symm.trans
      (eq_of_mem_of_notMem y hy z hz.2 hzG))
  · refine Subset.antisymm (subset_univ _) fun z _ => ?_
    by_cases hz : z ∈ ⋃ C, A C
    · exact Set.mem_union_left _ hz
    · exact Set.mem_union_right _ (mem_biUnion hz (hV z hz).2.1)

end Stacks.Topology.Dimension

end
