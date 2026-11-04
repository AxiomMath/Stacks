module

public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Subsets of quasi-compact subsets of locally Noetherian spaces (Stacks 0053, 0052)

In a locally Noetherian topological space every quasi-compact subset is covered by finitely many
Noetherian open subspaces, so it lies in a Noetherian subspace, a finite union of Noetherian
subspaces being Noetherian (Stacks 0053, `TopologicalSpace.NoetherianSpace.iUnion`). Any subset of
a Noetherian subspace is Noetherian (Stacks 0052, `TopologicalSpace.NoetherianSpace.of_subset`).
Hence every subset of a quasi-compact subset of a locally Noetherian space is a Noetherian
topological space in the subspace topology.

This is the topological reduction in the proof of Stacks 0E96.

## Main results

* `TopologicalSpace.noetherianSpace_of_subset_of_isCompact`: a subset of a quasi-compact subset of
  a locally Noetherian space is Noetherian.

## References

* [Stacks Project, Tag 0053](https://stacks.math.columbia.edu/tag/0053)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public section

open Set

namespace TopologicalSpace

/-- **A subset of a quasi-compact subset of a locally Noetherian space is Noetherian.** Let `X`
be locally Noetherian and `K ⊆ X` quasi-compact. Every point of `K` has a Noetherian open
neighbourhood, finitely many of them cover `K`, and their union is Noetherian by Stacks 0053;
any `T ⊆ K` lies in that union, so it is Noetherian by Stacks 0052. -/
theorem noetherianSpace_of_subset_of_isCompact {X : Type*} [TopologicalSpace X]
    (hX : IsLocallyNoetherianSpace X) {K T : Set X} (hK : IsCompact K) (hTK : T ⊆ K) :
    NoetherianSpace T := by
  choose U hUopen hxU hUnoeth using hX
  obtain ⟨t, ht⟩ : ∃ t : Finset X, K ⊆ ⋃ x ∈ t, U x :=
    hK.elim_finite_subcover U hUopen fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  have hunion : NoetherianSpace (⋃ x : (t : Set X), U x.1) := by
    have : ∀ x : (t : Set X), NoetherianSpace (U x.1) := fun x => hUnoeth x.1
    exact NoetherianSpace.iUnion (fun x : (t : Set X) => U x.1)
  have hsub : T ⊆ ⋃ x : (t : Set X), U x.1 := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (ht (hTK hy))
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hyx⟩
  exact NoetherianSpace.of_subset hsub

end TopologicalSpace
