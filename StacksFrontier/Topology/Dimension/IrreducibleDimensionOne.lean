module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Irreducible Jacobson spaces of Krull dimension one

In an irreducible Jacobson space of Krull dimension one the proper irreducible closed subsets
are exactly the singletons. Consequently a continuous map from an irreducible space into such a
space whose range contains at least two points has dense range.

## Main results

* `Stacks.Topology.Dimension.properIrreducibleClosed_eq_singleton`: a proper irreducible closed
  subset of an irreducible Jacobson space of dimension one is a singleton.
* `Stacks.Topology.Dimension.denseRange_of_nontrivial_of_topologicalKrullDim_eq_one`: a
  continuous map into such a space with at least two points in its range is dominant.
* `Stacks.Topology.Dimension.closed_irreducible_subset_eq_of_dim_one`: a closed subset of
  dimension one of an irreducible space of dimension one is the whole space.

## References

* [Stacks Project, Tag 0CCK](https://stacks.math.columbia.edu/tag/0CCK)
* [Stacks Project, Tag 0CCY](https://stacks.math.columbia.edu/tag/0CCY)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace Stacks.Topology.Dimension

/-- A proper irreducible closed subset is strictly below the whole space. -/
private theorem irreducibleCloseds_lt_univ {B : Type*} [TopologicalSpace B]
    (hB : IsIrreducible (Set.univ : Set B)) {Z : IrreducibleCloseds B}
    (hZ : (Z : Set B) ≠ Set.univ) : Z < ⟨Set.univ, hB, isClosed_univ⟩ :=
  lt_of_le_of_ne (Set.subset_univ _) fun h => hZ (congrArg IrreducibleCloseds.carrier h)

/-- **A proper irreducible closed subset of an irreducible Jacobson space of Krull dimension one
is a singleton.** -/
theorem properIrreducibleClosed_eq_singleton
    {Y : Type u} [TopologicalSpace Y] [IrreducibleSpace Y] [JacobsonSpace Y]
    (hdim : topologicalKrullDim Y = 1)
    (Z : IrreducibleCloseds Y) (hZ : Z.carrier ≠ Set.univ)
    {y : Y} (hy : y ∈ Z.carrier) : Z.carrier = {y} := by
  obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints
    ⟨y, hy⟩ Z.isClosed'.isLocallyClosed
  have hzc : IsClosed ({z} : Set Y) := mem_closedPoints_iff.mp hzclosed
  let W : IrreducibleCloseds Y := ⟨{z}, isIrreducible_singleton, hzc⟩
  have hWZ : W ≤ Z := Set.singleton_subset_iff.mpr hz
  have hZT := irreducibleCloseds_lt_univ (IrreducibleSpace.isIrreducible_univ Y) hZ
  rcases (Order.krullDim_le_one_iff.mp hdim.le) Z with hmin | hmax
  · have heq : W = Z := le_antisymm hWZ (hmin hWZ)
    obtain rfl : y = z := by simpa [← heq, W] using hy
    exact congrArg IrreducibleCloseds.carrier heq.symm
  · exact absurd hZT (not_lt_of_ge (hmax hZT.le))

/-- **A continuous map into an irreducible Jacobson space of Krull dimension one whose range has
at least two points has dense range.** -/
theorem denseRange_of_nontrivial_of_topologicalKrullDim_eq_one
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [IrreducibleSpace X] [IrreducibleSpace Y] [JacobsonSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hn : (Set.range f).Nontrivial)
    (hdim : topologicalKrullDim Y = 1) : DenseRange f := by
  show Dense (Set.range f)
  rw [dense_iff_closure_eq]
  by_contra h
  let Z : IrreducibleCloseds Y := ⟨closure (Set.range f), by
    apply IsIrreducible.closure
    convert (IrreducibleSpace.isIrreducible_univ X).image f hf.continuousOn using 1
    simp, isClosed_closure⟩
  have hZ : Z.carrier ≠ Set.univ := by simpa [Z] using h
  obtain ⟨a, ha, b, hb, hab⟩ := hn
  have hac := properIrreducibleClosed_eq_singleton hdim Z hZ (subset_closure ha)
  exact hab (Set.mem_singleton_iff.mp (hac ▸ subset_closure hb)).symm

/-- **A closed subset of dimension one of an irreducible space of dimension one is the whole
space.** -/
theorem closed_irreducible_subset_eq_of_dim_one
    {B : Type*} [TopologicalSpace B] {A : Set B}
    (hAclosed : IsClosed A) (hBirr : IsIrreducible (Set.univ : Set B))
    (hAdim : topologicalKrullDim A = 1) (hBdim : topologicalKrullDim B = 1) :
    A = Set.univ := by
  by_contra hne
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (IrreducibleCloseds A), l.length = 1 := by
    apply (Order.le_krullDim_iff (α := IrreducibleCloseds A) (n := 1)).mp
    rw [← topologicalKrullDim, hAdim, Nat.cast_one]
  let e : A → B := fun x => x.1
  let j := IrreducibleCloseds.map e continuous_subtype_val
  have hj : StrictMono j := IrreducibleCloseds.map_strictMono_of_isInducing
    (f := e) Topology.IsInducing.subtypeVal
  let q := l.map j hj
  have hqA : (q.last : Set B) ⊆ A := by
    show closure (e '' (l.last : Set A)) ⊆ A
    refine closure_minimal ?_ hAclosed
    rintro b ⟨a, _, rfl⟩
    exact a.2
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem A).mp hne
  have hqtop := irreducibleCloseds_lt_univ hBirr (Z := q.last)
    fun h => hb (hqA (h ▸ Set.mem_univ b))
  let q' := q.snoc _ hqtop
  have hdimB : (2 : ℕ) ≤ topologicalKrullDim B := by
    apply (Order.le_krullDim_iff (α := IrreducibleCloseds B) (n := 2)).mpr
    exact ⟨q', by simp [q', q, hl]⟩
  rw [hBdim] at hdimB
  exact absurd hdimB (by decide)

end Stacks.Topology.Dimension

end
