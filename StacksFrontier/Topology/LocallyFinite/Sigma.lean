module

public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Combining locally finite families indexed over a sigma type

Let `T : I → Set Y` be a locally finite collection of subsets of a topological space and, for
each index `i`, let `W i : J i → Set Y` be a locally finite collection whose members are
contained in `T i`. Then the collection indexed by `Σ i, J i` obtained by combining all the
`W i` is again locally finite.

## Main results

* `locallyFinite_sigma_of_subset`: local finiteness of the combined collection.

## Implementation notes

The neighbourhood witnessing local finiteness of the combined collection at a point `x` is the
intersection of a neighbourhood `U` witnessing local finiteness of `T` at `x` with the
neighbourhoods witnessing local finiteness of the `W i` at `x`, taken over the finitely many
indices `i` for which `T i` meets `U`.

A locally finite collection of subsets of a topological space, Stacks 0BDS, is Mathlib's
`LocallyFinite`.

## References

* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS)
-/

@[expose] public section

universe u v w

/-- Let `T : I → Set Y` be a locally finite collection of subsets of a topological space and,
for each `i`, let `W i : J i → Set Y` be a locally finite collection with `W i j ⊆ T i` for all
`j`. Then the combined collection `fun ij : Σ i, J i ↦ W ij.1 ij.2` is locally finite. -/
@[stacks 0EQ8 "local finiteness of the combined family"]
theorem locallyFinite_sigma_of_subset {Y : Type u} [TopologicalSpace Y] {I : Type v}
    {J : I → Type w} {T : I → Set Y} (hT : LocallyFinite T) {W : ∀ i, J i → Set Y}
    (hW : ∀ i, LocallyFinite (W i)) (hWT : ∀ i j, W i j ⊆ T i) :
    LocallyFinite fun ij : Σ i, J i ↦ W ij.1 ij.2 := by
  intro x
  obtain ⟨U, hU, hUfin⟩ := hT x
  choose V hV hVfin using fun i ↦ hW i x
  refine ⟨U ∩ ⋂ i ∈ {i | (T i ∩ U).Nonempty}, V i,
    Filter.inter_mem hU ((Filter.biInter_mem hUfin).2 fun i _ ↦ hV i), ?_⟩
  refine (hUfin.biUnion fun i _ ↦ (hVfin i).image (Sigma.mk i)).subset ?_
  rintro ⟨i, j⟩ ⟨y, hyW, hyU, hyV⟩
  have hi : i ∈ {i | (T i ∩ U).Nonempty} := ⟨y, hWT i j hyW, hyU⟩
  exact Set.mem_biUnion hi ⟨j, ⟨y, hyW, Set.mem_iInter₂.1 hyV i hi⟩, rfl⟩

end
