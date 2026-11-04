module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Prod

/-!
# The topological genus of a numerical type

The intersection matrix of a numerical type is the adjacency matrix of a
connected graph on its components. Its cycle rank `1 - n + e`, the *topological
genus*, is nonnegative because the graph is connected.

## Main definitions

* `AlgebraicGeometry.NumericalType.edgeCount`: the number of pairs of distinct
  components with nonzero intersection.
* `AlgebraicGeometry.NumericalType.intersectionGraph`: the graph on the components in which
  distinct components are adjacent when their intersection number is positive.

## Main results

* `AlgebraicGeometry.NumericalType.one_sub_componentCount_add_edgeCount_nonneg`.

## References

* [Stacks Project, Tag 0C78](https://stacks.math.columbia.edu/tag/0C78)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The number of pairs of components `i < j` whose intersection number is
positive. -/
public def edgeCount (T : NumericalType) : ℕ :=
  ((Finset.univ : Finset (Fin T.componentCount × Fin T.componentCount)).filter
    fun ij => ij.1 < ij.2 ∧ 0 < T.intersection ij.1 ij.2).card

/-- The simple graph on the components of `T` in which distinct components `i` and `j` are
adjacent when their intersection number is positive. -/
public def intersectionGraph (T : NumericalType) : SimpleGraph (Fin T.componentCount) where
  Adj i j := i ≠ j ∧ 0 < T.intersection i j
  symm := ⟨fun i j h ↦ ⟨h.1.symm, by simpa [T.intersection_symm i j] using h.2⟩⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

/-- The intersection graph of a numerical type is connected. -/
public lemma intersectionGraph_connected (T : NumericalType) :
    (intersectionGraph T).Connected := by
  constructor
  intro u v
  by_contra huv
  refine T.connected ⟨{w | (intersectionGraph T).Reachable u w}, ⟨u, SimpleGraph.Reachable.rfl⟩,
    fun hI ↦ huv (Set.eq_univ_iff_forall.mp hI v), fun i hi j hj ↦ ?_⟩
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  exact le_antisymm (not_lt.mp fun hpos ↦ hj (hi.trans (SimpleGraph.Adj.reachable ⟨hij, hpos⟩)))
    (T.intersection_nonneg i j hij)

/-- The edge count of `T` is the number of edges of its intersection graph. -/
public lemma edgeCount_eq_card_edgeFinset (T : NumericalType) :
    edgeCount T = Nat.card (intersectionGraph T).edgeSet := by
  classical
  let _ : Fintype (intersectionGraph T).edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  unfold edgeCount
  refine Finset.card_bij (fun (ij : Fin T.componentCount × Fin T.componentCount) _ ↦
    s(ij.1, ij.2)) ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨i, j⟩ ⟨hij, hpos⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hij.ne, hpos⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨i, j⟩ ⟨hij, -⟩ ⟨k, l⟩ ⟨hkl, -⟩ he
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · change i = l ∧ j = k at h
      obtain ⟨rfl, rfl⟩ := h
      exact (hij.asymm hkl).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | hf i j =>
      have hadj : (intersectionGraph T).Adj i j := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      by_cases hij : i < j
      · exact ⟨(i, j), by simp [hij, hadj.2], rfl⟩
      · have hji : j < i := lt_of_le_of_ne (not_lt.mp hij) hadj.1.symm
        exact ⟨(j, i), by simpa [hji, T.intersection_symm j i] using hadj.2, Sym2.eq_swap⟩

/-- For a numerical type, one minus the number of components plus the number of
positive-intersection pairs is nonnegative. -/
@[stacks 0C78]
public lemma one_sub_componentCount_add_edgeCount_nonneg (T : NumericalType) :
    0 ≤ (1 : ℤ) - T.componentCount + edgeCount T := by
  have h := (intersectionGraph_connected T).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← edgeCount_eq_card_edgeFinset] at h
  omega

end AlgebraicGeometry.NumericalType
