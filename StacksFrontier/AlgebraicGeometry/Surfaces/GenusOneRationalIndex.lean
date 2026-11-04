module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkClassification
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.TopologicalGenus

/-!
# Minimal numerical types of genus one with a component of multiplicity and weight one

Section 0CEG of the Stacks project proves semistable reduction in genus one by running through
the classification of minimal numerical types of genus one (Tag 0C8T) for a numerical type that
has an index `i` with `mᵢ = wᵢ = 1`; such an index exists for the numerical type of a minimal
model of a curve with a rational point (Tag 0CE8). The source sorts the configurations on the
list that have such an index into two cases:

* (A) the configurations whose intersection graph is a tree, `e = n - 1` edges for `n`
  components; for these, after the scalings of the list are forced to be one by the index, every
  multiplicity and every intersection number is less than `7`;
* (B) the cycles on at least three components, with all multiplicities and weights one and all
  component genera zero.

This file proves that sorting. A configuration on the list whose scalings are forced to be one
is, in particular, a configuration whose coefficient tables are those printed in the list, so the
check for the twenty-six finite tables is a finite computation; for the seven unbounded families
the edges are counted by an injection into `{0, …, n - 2}`.

It also records the linear algebra feeding the source's two cases: for a prime `ℓ` prime to
every positive intersection number and every multiplicity, the `ℓ`-torsion of the Picard group
of a numerical type has dimension at most its topological genus `1 - n + e` (Tag 0C6X through
Tag 0CE7), so it vanishes in case (A) and has dimension at most one in case (B).

## Main results

* `AlgebraicGeometry.NumericalType.edgeCount_eq_card_of_equiv` — the number of edges of a
  numerical type, read through a relabelling of its components.
* `AlgebraicGeometry.NumericalType.tree_or_cycle_of_isMinimal_of_genus_eq_one` — the sorting of
  the minimal numerical types of genus one with an index of multiplicity and weight one into the
  source's cases (A) and (B).
* `AlgebraicGeometry.NumericalType.finrank_torsionBy_picardGroup_add_componentCount_le` — the
  bound `dim Pic(T)[ℓ] + n ≤ 1 + e` for `ℓ` prime to the intersection numbers and
  multiplicities.

## References

* [Stacks Project, Section 0CEG](https://stacks.math.columbia.edu/tag/0CEG)
* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
* [Stacks Project, Tag 0C6X](https://stacks.math.columbia.edu/tag/0C6X)
-/

@[expose] public section

open Finset

namespace AlgebraicGeometry.NumericalType

/-! ### Counting edges -/

/-- For a symmetric matrix, the ordered pairs of distinct indices with a positive entry are
twice as many as the pairs `i < j` with a positive entry. -/
theorem two_mul_card_filter_lt_eq_card_filter_ne {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hA : ∀ i j, A i j = A j i) :
    2 * (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2).card =
      (univ.filter fun q : Fin n × Fin n => q.1 ≠ q.2 ∧ 0 < A q.1 q.2).card := by
  classical
  have hsplit : (univ.filter fun q : Fin n × Fin n => q.1 ≠ q.2 ∧ 0 < A q.1 q.2) =
      (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2) ∪
        (univ.filter fun q : Fin n × Fin n => q.2 < q.1 ∧ 0 < A q.1 q.2) := by
    ext q
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h, h'⟩
      rcases lt_or_gt_of_ne h with h | h
      exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      exacts [⟨h.ne, h'⟩, ⟨h.ne', h'⟩]
  have hdisj : Disjoint (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2)
      (univ.filter fun q : Fin n × Fin n => q.2 < q.1 ∧ 0 < A q.1 q.2) :=
    Finset.disjoint_filter.2 fun _ _ h h' => lt_asymm h.1 h'.1
  have hswap : (univ.filter fun q : Fin n × Fin n => q.2 < q.1 ∧ 0 < A q.1 q.2).card =
      (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2).card := by
    refine Finset.card_bij (fun q _ => q.swap) ?_ ?_ ?_
    · intro q hq
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hq ⊢
      exact ⟨hq.1, by rw [hA]; exact hq.2⟩
    · intro a _ b _ h
      simpa using congrArg Prod.swap h
    · intro b hb
      refine ⟨b.swap, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hb ⊢
      exact ⟨hb.1, by rw [hA]; exact hb.2⟩
  rw [hsplit, card_union_of_disjoint hdisj, hswap]
  ring

/-- **The number of edges of a numerical type through a relabelling.** If a relabelling `e` of
the components carries the positive entries of a symmetric matrix `A` to the positive
intersection numbers, then the number of edges of the numerical type is the number of pairs
`i < j` with `A i j > 0`. -/
theorem edgeCount_eq_card_of_equiv (T : NumericalType) {n : ℕ}
    (e : Fin n ≃ Fin T.componentCount) (A : Fin n → Fin n → ℤ) (hA : ∀ i j, A i j = A j i)
    (h : ∀ i j, 0 < T.intersection (e i) (e j) ↔ 0 < A i j) :
    edgeCount T = (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2).card := by
  classical
  have h1 := two_mul_card_filter_lt_eq_card_filter_ne T.intersection T.intersection_symm
  have h2 := two_mul_card_filter_lt_eq_card_filter_ne A hA
  have h3 : (univ.filter fun q : Fin n × Fin n => q.1 ≠ q.2 ∧ 0 < A q.1 q.2).card =
      (univ.filter fun q : Fin T.componentCount × Fin T.componentCount =>
        q.1 ≠ q.2 ∧ 0 < T.intersection q.1 q.2).card := by
    refine Finset.card_bij (fun q _ => (e q.1, e q.2)) ?_ ?_ ?_
    · intro q hq
      simp only [mem_filter, mem_univ, true_and] at hq ⊢
      exact ⟨fun h' => hq.1 (e.injective h'), (h _ _).2 hq.2⟩
    · intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (e.injective hab.1) (e.injective hab.2)
    · intro b hb
      refine ⟨(e.symm b.1, e.symm b.2), ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      exact ⟨fun h' => hb.1 (by simpa using congrArg e h'), (h _ _).1 (by simpa using hb.2)⟩
  unfold edgeCount
  omega

/-- A family of pairs `i < j` of indices among `n ≥ 1` has at most `n - 1` members as soon as it
injects into `{0, …, n - 2}`. -/
theorem card_filter_add_one_le_of_injOn {n : ℕ} (hn : 1 ≤ n) (P : Fin n × Fin n → Prop)
    [DecidablePred P] (φ : Fin n × Fin n → ℕ) (hφ : ∀ q, P q → φ q < n - 1)
    (hinj : ∀ q q', P q → P q' → φ q = φ q' → q = q') :
    (univ.filter P).card + 1 ≤ n := by
  have hle : (univ.filter P).card ≤ (range (n - 1)).card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro q hq
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hq
      simpa using hφ q hq
    · intro q hq q' hq' hqq'
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hq hq'
      exact hinj q q' hq hq' hqq'
  rw [card_range] at hle
  omega

/-! ### The unbounded families -/

namespace GenusOne

/-- Off the diagonal, the intersection matrix of an unbounded family is the edge coefficient of
the smaller and the larger endpoint. -/
theorem longIntersection_of_lt (f : LongFamily) (n : ℕ) {i j : Fin n} (hij : i < j) :
    longIntersection f n i j = longEdge f n i.val j.val := by
  have hij' : i.val < j.val := hij
  simp [longIntersection, hij.ne, min_eq_left hij'.le, max_eq_right hij'.le]

/-- The intersection matrix of an unbounded family is symmetric. -/
theorem longIntersection_comm (f : LongFamily) (n : ℕ) (i j : Fin n) :
    longIntersection f n i j = longIntersection f n j i := by
  by_cases h : i = j
  · rw [h]
  · simp only [longIntersection, h, Ne.symm h, if_false, min_comm, max_comm]

/-- A pair `i < j` with a positive intersection coefficient has a positive edge coefficient. -/
private theorem lt_and_pos_longEdge_of_pos_longIntersection (f : LongFamily) (n : ℕ)
    {q : Fin n × Fin n} (hq : q.1 < q.2) (h : 0 < longIntersection f n q.1 q.2) :
    q.1.val < q.2.val ∧ 0 < longEdge f n q.1.val q.2.val :=
  ⟨hq, by rwa [longIntersection_of_lt f n hq] at h⟩

/-- Every multiplicity coefficient of an unbounded family is at most two. -/
theorem longMultiplicity_le_two (f : LongFamily) (n : ℕ) (i : Fin n) :
    longMultiplicity f n i ≤ 2 := by
  cases f <;> simp only [longMultiplicity] <;> (try split_ifs) <;> norm_num

/-- Every intersection coefficient of an unbounded family is at most four. -/
theorem longIntersection_le_four (f : LongFamily) (n : ℕ) (i j : Fin n) :
    longIntersection f n i j ≤ 4 := by
  unfold longIntersection
  split_ifs with h
  · cases f <;> simp only [longWeight] <;> (try split_ifs) <;> norm_num
  · cases f <;> simp only [longEdge] <;> (try split_ifs) <;> norm_num

/-- Pairs `i < j` all of whose positive entries join consecutive indices number at most
`n - 1`. -/
theorem card_filter_add_one_le_of_consecutive {n : ℕ} (hn : 1 ≤ n) (A : Fin n → Fin n → ℤ)
    (hA : ∀ q : Fin n × Fin n, q.1 < q.2 → 0 < A q.1 q.2 → q.2.val = q.1.val + 1) :
    (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2).card + 1 ≤ n := by
  refine card_filter_add_one_le_of_injOn hn _ (fun q => q.1.val) ?_ ?_
  · intro q hq
    have h1 := hA q hq.1 hq.2
    have h2 := q.2.isLt
    omega
  · intro q q' hq hq' h
    have h1 := hA q hq.1 hq.2
    have h2 := hA q' hq'.1 hq'.2
    change q.1.val = q'.1.val at h
    exact Prod.ext (Fin.ext h) (Fin.ext (by omega))

/-- Pairs `i < j` all of whose positive entries join consecutive indices below `n - 1`, or
`n - 3` to `n - 1`, or one of `0` and `1` to `2`, number at most `n - 1`, for `n ≥ 6`. -/
theorem card_filter_add_one_le_of_fork {n : ℕ} (hn : 6 ≤ n) (A : Fin n → Fin n → ℤ)
    (hA : ∀ q : Fin n × Fin n, q.1 < q.2 → 0 < A q.1 q.2 →
      (q.2.val = q.1.val + 1 ∧ q.2.val < n - 1) ∨ (q.1.val = n - 3 ∧ q.2.val = n - 1) ∨
        (q.1.val ≤ 1 ∧ q.2.val = 2))
    (hA' : (∃ q : Fin n × Fin n, q.1 < q.2 ∧ 0 < A q.1 q.2 ∧ q.1.val = 0 ∧ q.2.val = 2) →
      ∀ q : Fin n × Fin n, q.1 < q.2 → 0 < A q.1 q.2 → q.1.val = 0 → q.2.val = 2) :
    (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ 0 < A q.1 q.2).card + 1 ≤ n := by
  refine card_filter_add_one_le_of_injOn (by omega) _
    (fun q => if q.2.val = n - 1 then n - 2 else q.1.val) ?_ ?_
  · intro q hq
    have h1 := hA q hq.1 hq.2
    have h2 := q.2.isLt
    have h3 : q.1.val < q.2.val := hq.1
    show (if q.2.val = n - 1 then n - 2 else q.1.val) < n - 1
    split_ifs <;> omega
  · intro q q' hq hq' h
    have h1 := hA q hq.1 hq.2
    have h2 := hA q' hq'.1 hq'.2
    have h3 : q.1.val < q.2.val := hq.1
    have h4 : q'.1.val < q'.2.val := hq'.1
    change (if q.2.val = n - 1 then n - 2 else q.1.val) =
      (if q'.2.val = n - 1 then n - 2 else q'.1.val) at h
    by_cases h0 : q.1.val = 0 ∧ q.2.val = 2
    · have h5 := hA' ⟨q, hq.1, hq.2, h0.1, h0.2⟩ q' hq'.1 hq'.2
      split_ifs at h <;>
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    · by_cases h0' : q'.1.val = 0 ∧ q'.2.val = 2
      · have h5 := hA' ⟨q', hq'.1, hq'.2, h0'.1, h0'.2⟩ q hq.1 hq.2
        split_ifs at h <;>
          exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      · split_ifs at h <;> exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The edges of an unbounded family other than the cycle form a tree: there are at most
`n - 1` pairs `i < j` with a positive coefficient. The chains have their edges between
consecutive indices, the forks between consecutive indices below `n - 1` and from `n - 3` to
`n - 1`, and the double fork in addition from `0` and from `1` to `2`. -/
theorem card_filter_longIntersection_add_one_le (f : LongFamily) (hf : f ≠ .cycle) {n : ℕ}
    (hn : 6 ≤ n) :
    (univ.filter fun q : Fin n × Fin n =>
      q.1 < q.2 ∧ 0 < longIntersection f n q.1 q.2).card + 1 ≤ n := by
  cases f with
  | cycle => exact absurd rfl hf
  | upUp | upDown | downUp =>
    refine card_filter_add_one_le_of_consecutive (by omega) _ fun q hq hpos => ?_
    obtain ⟨hq', hpos⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hq hpos
    simp only [longEdge] at hpos
    split_ifs at hpos <;> omega
  | forkUp | forkDown =>
    refine card_filter_add_one_le_of_fork hn _ (fun q hq hpos => ?_) ?_
    · obtain ⟨hq', hpos⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hq hpos
      simp only [longEdge] at hpos
      split_ifs at hpos <;> omega
    · rintro ⟨q, hq, hpos, h0, h2⟩
      obtain ⟨hq', hpos⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hq hpos
      simp only [longEdge] at hpos
      split_ifs at hpos <;> omega
  | doubleFork =>
    refine card_filter_add_one_le_of_fork hn _ (fun q hq hpos => ?_) ?_
    · obtain ⟨hq', hpos⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hq hpos
      simp only [longEdge] at hpos
      split_ifs at hpos <;> omega
    · rintro - q hq hpos h0
      obtain ⟨hq', hpos⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hq hpos
      simp only [longEdge] at hpos
      split_ifs at hpos <;> omega

/-- A pair `i < j` is an edge of the cycle on `n` components exactly when `j = i + 1` or
`(i, j) = (0, n - 1)`. -/
private theorem lt_and_pos_longIntersection_cycle_iff {n : ℕ} (q : Fin n × Fin n) :
    (q.1 < q.2 ∧ 0 < longIntersection .cycle n q.1 q.2) ↔
      (q.1.val < q.2.val ∧ (q.2.val = q.1.val + 1 ∨ (q.1.val = 0 ∧ q.2.val = n - 1))) := by
  obtain ⟨a, b⟩ := q
  constructor
  · rintro ⟨hab, h⟩
    obtain ⟨-, h⟩ := lt_and_pos_longEdge_of_pos_longIntersection _ n hab h
    simp only [longEdge] at h
    split_ifs at h with h1 <;> first | omega | exact ⟨hab, h1⟩
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    rw [longIntersection_of_lt _ n hab]
    simp only [longEdge]
    rw [if_pos h]
    norm_num

/-- The cycle on `n ≥ 3` components has exactly `n` edges: the pairs `(i, i + 1)` for `i < n - 1`
and the pair `(0, n - 1)`. -/
theorem card_filter_longIntersection_cycle {n : ℕ} (hn : 3 ≤ n) :
    (univ.filter fun q : Fin n × Fin n =>
      q.1 < q.2 ∧ 0 < longIntersection .cycle n q.1 q.2).card = n := by
  classical
  have hpos := @lt_and_pos_longIntersection_cycle_iff n
  apply le_antisymm
  · have hle : (univ.filter fun q : Fin n × Fin n =>
        q.1 < q.2 ∧ 0 < longIntersection .cycle n q.1 q.2).card ≤ (range n).card := by
      refine Finset.card_le_card_of_injOn
        (fun q => if q.1.val = 0 ∧ q.2.val = n - 1 then n - 1 else q.1.val) ?_ ?_
      · intro q hq
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, hpos] at hq
        have := q.2.isLt
        simp only [coe_range, Set.mem_Iio]
        split_ifs <;> omega
      · intro q hq q' hq' h
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, hpos] at hq hq'
        have := q.2.isLt
        have := q'.2.isLt
        simp only at h
        split_ifs at h <;> exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    simpa using hle
  · have hle : (univ : Finset (Fin n)).card ≤ (univ.filter fun q : Fin n × Fin n =>
        q.1 < q.2 ∧ 0 < longIntersection .cycle n q.1 q.2).card := by
      refine Finset.card_le_card_of_injOn
        (fun i : Fin n => if h : i.val + 1 < n then ((i, ⟨i.val + 1, h⟩) : Fin n × Fin n)
          else (⟨0, by omega⟩, ⟨n - 1, by omega⟩)) ?_ ?_
      · intro i _
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, hpos]
        split_ifs with h
        · exact ⟨by simp only; omega, Or.inl rfl⟩
        · exact ⟨by simp only; omega, Or.inr ⟨rfl, rfl⟩⟩
      · intro i _ j _ h
        have hi := i.isLt
        have hj := j.isLt
        simp only at h
        split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq, Fin.ext_iff] at h <;>
          exact Fin.ext (by omega)
    simpa using hle

/-- Off the diagonal, the intersection coefficient of two indices of the cycle on `n ≥ 3`
components is the number of ways of writing one of them as the other plus or minus one,
modulo `n`. -/
theorem longIntersection_cycle_of_ne {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    longIntersection .cycle n i j =
      (if j.val = (i.val + 1) % n then 1 else 0) + (if i.val = (j.val + 1) % n then 1 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hmod : ∀ a : ℕ, a < n → (a + 1) % n = if a + 1 = n then 0 else a + 1 := by
    intro a ha
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hmod i.val hi, hmod j.val hj]
  simp only [longIntersection, hij, if_false, longEdge]
  rcases lt_or_gt_of_ne hij' with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> omega

/-! ### The finite tables -/

/-- A coefficient table, as in `AlgebraicGeometry.NumericalType.GenusOne.finitePatterns`, is
*a tree or a cycle* if either its positive entries above the diagonal number at most one less
than its size and all its multiplicity and intersection coefficients are less than `7`, or it
has at least three rows, all multiplicity and weight coefficients one, and intersection
coefficients those of the cycle. -/
def IsTreeOrCycleTable (p : List ℤ × List ℤ × List (List ℤ)) : Prop :=
  ((univ.filter fun q : Fin p.1.length × Fin p.1.length =>
      q.1 < q.2 ∧ 0 < (p.2.2.getD q.1.val []).getD q.2.val 0).card + 1 ≤ p.1.length ∧
    (∀ i : Fin p.1.length, p.1.getD i.val 0 < 7) ∧
    ∀ i j : Fin p.1.length, (p.2.2.getD i.val []).getD j.val 0 < 7) ∨
  (3 ≤ p.1.length ∧ (∀ i : Fin p.1.length, p.1.getD i.val 0 = 1 ∧ p.2.1.getD i.val 0 = 1) ∧
    ∀ i j : Fin p.1.length,
      (p.2.2.getD i.val []).getD j.val 0 = longIntersection .cycle p.1.length i j)

/-- Whether a coefficient table is a tree or a cycle is decidable. -/
instance (p : List ℤ × List ℤ × List (List ℤ)) : Decidable (IsTreeOrCycleTable p) := by
  unfold IsTreeOrCycleTable
  infer_instance

/-- Each of the twenty-six exceptional coefficient tables of genus one is a tree or a cycle; the
cycles are the ones on three, four and five components. -/
theorem forall_isTreeOrCycleTable_finitePatterns :
    ∀ p ∈ finitePatterns, IsTreeOrCycleTable p := by
  decide

end GenusOne

/-! ### Cases (A) and (B) of Section 0CEG -/

/-- If a coefficient of a positive scaling `s` is one at a component, the scaling is one. -/
private theorem scaling_eq_one {n k : ℕ} (e : Fin n ≃ Fin k) (f : Fin k → ℤ) (c : Fin n → ℤ)
    {s : ℤ} (hs : 0 < s) (hmul : ∀ i, f (e i) = c i * s) {i₀ : Fin k} (h : f i₀ = 1) : s = 1 := by
  have h1 : c (e.symm i₀) * s = 1 := by rw [← hmul, e.apply_symm_apply, h]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega

/-- Case (A) of Section 0CEG for the configuration with one component. -/
private theorem tree_or_cycle_of_matchesCoefficients_one (T : NumericalType)
    (i₀ : Fin T.componentCount) (hm : T.multiplicity i₀ = 1)
    (h : MatchesCoefficients T 1 (fun _ => 1) (fun _ => 1) (fun _ _ => 0) (fun _ => 1)) :
    (edgeCount T + 1 ≤ T.componentCount ∧ (∀ i, T.multiplicity i < 7) ∧
        ∀ i j, T.intersection i j < 7) ∨
      ((∀ i, T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.componentGenus i = 0) ∧
        ∃ (n : ℕ) (e : Fin n ≃ Fin T.componentCount), 3 ≤ n ∧
          ∀ i j, T.intersection (e i) (e j) = GenusOne.longIntersection .cycle n i j) := by
  obtain ⟨e, m, w, hm0, -, hmul, -, hint, -⟩ := h
  beta_reduce at hmul hint
  have hall : ∀ i, i = e 0 := fun i => by
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrArg e (Subsingleton.elim _ _)
  have hm1 : m = 1 := scaling_eq_one e _ _ hm0 hmul hm
  left
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · have hcount : T.componentCount = 1 := by simpa using (Fintype.card_congr e).symm
    have h0 : edgeCount T = 0 := by
      rw [edgeCount_eq_card_of_equiv T e (fun _ _ => 0) (fun _ _ => rfl)
        (fun i j => by rw [hint]; simp)]
      simp
    omega
  · rw [hall i, hmul 0, hm1]
    norm_num
  · rw [hall i, hall j, hint]
    norm_num

open GenusOne in
/-- Cases (A) and (B) of Section 0CEG for the twenty-six finite tables. -/
private theorem tree_or_cycle_of_matchesFinite (T : NumericalType) (i₀ : Fin T.componentCount)
    (hm : T.multiplicity i₀ = 1) (hw : T.weight i₀ = 1)
    {p : List ℤ × List ℤ × List (List ℤ)} (hp : p ∈ finitePatterns)
    (h : MatchesFinite T p.1 p.2.1 p.2.2) :
    (edgeCount T + 1 ≤ T.componentCount ∧ (∀ i, T.multiplicity i < 7) ∧
        ∀ i j, T.intersection i j < 7) ∨
      ((∀ i, T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.componentGenus i = 0) ∧
        ∃ (n : ℕ) (e : Fin n ≃ Fin T.componentCount), 3 ≤ n ∧
          ∀ i j, T.intersection (e i) (e j) = longIntersection .cycle n i j) := by
  unfold MatchesFinite MatchesCoefficients at h
  obtain ⟨e, m, w, hm0, hw0, hmul, hwt, hint, hgen⟩ := h
  beta_reduce at hmul hwt hint hgen
  have hm1 : m = 1 := scaling_eq_one e _ _ hm0 hmul hm
  have hw1 : w = 1 := scaling_eq_one e _ _ hw0 hwt hw
  have hlen : p.1.length = T.componentCount := by simpa using Fintype.card_congr e
  rcases forall_isTreeOrCycleTable_finitePatterns p hp with ⟨hcnt, hmc, hac⟩ |
    ⟨h3, h11, hcyc⟩
  · left
    have hsymm : ∀ i j : Fin p.1.length, (p.2.2.getD i.val []).getD j.val 0 =
        (p.2.2.getD j.val []).getD i.val 0 := by
      intro i j
      have h1 := hint i j
      rw [T.intersection_symm, hint j i, hw1, mul_one, mul_one] at h1
      exact h1.symm
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · rw [edgeCount_eq_card_of_equiv T e _ hsymm (fun i j => by rw [hint, hw1, mul_one])]
      omega
    · obtain ⟨j, rfl⟩ := e.surjective i
      rw [hmul, hm1, mul_one]
      exact hmc j
    · obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      rw [hint, hw1, mul_one]
      exact hac i j
  · right
    refine ⟨fun i => ?_, p.1.length, e, h3, fun i j => by rw [hint, hw1, mul_one, hcyc]⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨by rw [hmul, hm1, mul_one, (h11 j).1], by rw [hwt, hw1, mul_one, (h11 j).2],
      by simpa using hgen j⟩

open GenusOne in
/-- Cases (A) and (B) of Section 0CEG for the seven unbounded families. -/
private theorem tree_or_cycle_of_matchesCoefficients_long (T : NumericalType)
    (i₀ : Fin T.componentCount) (hm : T.multiplicity i₀ = 1) (hw : T.weight i₀ = 1)
    {n : ℕ} {f : LongFamily} (hn : 6 ≤ n)
    (h : MatchesCoefficients T n (longMultiplicity f n) (longWeight f n) (longIntersection f n)) :
    (edgeCount T + 1 ≤ T.componentCount ∧ (∀ i, T.multiplicity i < 7) ∧
        ∀ i j, T.intersection i j < 7) ∨
      ((∀ i, T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.componentGenus i = 0) ∧
        ∃ (n : ℕ) (e : Fin n ≃ Fin T.componentCount), 3 ≤ n ∧
          ∀ i j, T.intersection (e i) (e j) = longIntersection .cycle n i j) := by
  obtain ⟨e, m, w, hm0, hw0, hmul, hwt, hint, hgen⟩ := h
  have hm1 : m = 1 := scaling_eq_one e _ _ hm0 hmul hm
  have hw1 : w = 1 := scaling_eq_one e _ _ hw0 hwt hw
  by_cases hf : f = .cycle
  · subst hf
    right
    refine ⟨fun i => ?_, n, e, by omega, fun i j => by rw [hint, hw1, mul_one]⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨by rw [hmul, hm1]; simp [longMultiplicity], by rw [hwt, hw1]; simp [longWeight],
      by simpa using hgen j⟩
  · left
    have hlen : n = T.componentCount := by simpa using Fintype.card_congr e
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · rw [edgeCount_eq_card_of_equiv T e (longIntersection f n) (longIntersection_comm f n)
        (fun i j => by rw [hint, hw1, mul_one])]
      have := card_filter_longIntersection_add_one_le f hf hn
      omega
    · obtain ⟨j, rfl⟩ := e.surjective i
      rw [hmul, hm1, mul_one]
      have := longMultiplicity_le_two f n j
      omega
    · obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      rw [hint, hw1, mul_one]
      have := longIntersection_le_four f n i j
      omega

open GenusOne in
/-- **The two cases of Section 0CEG.** Let `T` be a minimal numerical type of genus one with an
index `i₀` such that `m_{i₀} = w_{i₀} = 1`. Then either

* (A) the intersection graph of `T` has at most `n - 1` edges for `n` components, and every
  multiplicity and every intersection number of `T` is less than `7`; or
* (B) every multiplicity and every weight of `T` is one, every component genus is zero, and up
  to a relabelling of the components `T` is the cycle on `n ≥ 3` components.

The index forces the two scalings of the classification (Tag 0C8T) to be one, after which the
configurations are read off from their tables: case (A) consists of the configuration with one
component, the twenty-three finite tables which are trees and the six unbounded families other
than the cycle; case (B) of the cycles on three, four and five components and the unbounded
family of cycles. -/
theorem tree_or_cycle_of_isMinimal_of_genus_eq_one (T : NumericalType) (hmin : IsMinimal T)
    (hgenus : genus T = 1) (i₀ : Fin T.componentCount) (hm : T.multiplicity i₀ = 1)
    (hw : T.weight i₀ = 1) :
    (edgeCount T + 1 ≤ T.componentCount ∧ (∀ i, T.multiplicity i < 7) ∧
        ∀ i j, T.intersection i j < 7) ∨
      ((∀ i, T.multiplicity i = 1 ∧ T.weight i = 1 ∧ T.componentGenus i = 0) ∧
        ∃ (n : ℕ) (e : Fin n ≃ Fin T.componentCount), 3 ≤ n ∧
          ∀ i j, T.intersection (e i) (e j) = longIntersection .cycle n i j) := by
  rcases (isMinimal_and_genus_eq_one_iff T).1 ⟨hmin, hgenus⟩ with h | ⟨p, hp, h⟩ |
    ⟨n, f, hn, h⟩
  · exact tree_or_cycle_of_matchesCoefficients_one T i₀ hm h
  · exact tree_or_cycle_of_matchesFinite T i₀ hm hw hp h
  · exact tree_or_cycle_of_matchesCoefficients_long T i₀ hm hw hn h

open GenusOne in
/-- **A cycle has topological genus one.** A numerical type which, up to a relabelling of its
components, has the intersection numbers of the cycle on `n ≥ 3` components has `n` edges, so
its topological genus `1 - n + e` is one. -/
theorem topologicalGenus_eq_one_of_cycle (T : NumericalType) {n : ℕ}
    (e : Fin n ≃ Fin T.componentCount) (hn : 3 ≤ n)
    (h : ∀ i j, T.intersection (e i) (e j) = longIntersection .cycle n i j) :
    topologicalGenus T = 1 := by
  have hcount : n = T.componentCount := by simpa using Fintype.card_congr e
  have hedge : edgeCount T = n := by
    rw [edgeCount_eq_card_of_equiv T e (longIntersection .cycle n)
      (longIntersection_comm .cycle n) (fun i j => by rw [h]),
      card_filter_longIntersection_cycle hn]
  unfold topologicalGenus
  omega

/-! ### Prime torsion in the Picard group -/

/-- The `n`-torsion of a finitely generated abelian group is finite for `n ≠ 0`. -/
theorem finite_torsionBy_int {H : Type*} [AddCommGroup H] [Module.Finite ℤ H] {n : ℤ}
    (hn : n ≠ 0) : Finite (Submodule.torsionBy ℤ H n) :=
  Module.finite_of_fg_torsion _ fun x =>
    ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, Submodule.smul_torsionBy n x⟩

/-- The dimension of the `ℓ`-torsion is monotone along an injective map into a finitely
generated abelian group. -/
private theorem finrank_torsionBy_le_of_injective {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Module.Finite ℤ H] (ℓ : ℕ) [Fact ℓ.Prime] (f : G →+ H) (hf : Function.Injective f) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy G (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy H (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy G (ℓ : ℤ)) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy H (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy G (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy H (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have hfin : Finite (AddSubgroup.torsionBy H (ℓ : ℤ)) :=
    finite_torsionBy_int (by exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero)
  have : Module.Finite (ZMod ℓ) (AddSubgroup.torsionBy H (ℓ : ℤ)) := Module.Finite.of_finite
  let F : AddSubgroup.torsionBy G (ℓ : ℤ) →+ AddSubgroup.torsionBy H (ℓ : ℤ) :=
    { toFun := fun x => ⟨f x, by
        apply AddSubgroup.torsionBy.nsmul_iff.mpr
        have hx := (AddSubgroup.torsionBy.nsmul_iff (n := ℓ)).mp x.property
        rw [← map_nsmul]
        simpa using congrArg f hx⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  exact LinearMap.finrank_le_finrank_of_injective (f := AddMonoidHom.toZModLinearMap ℓ F)
    fun x y hxy => Subtype.ext <| hf <|
      congrArg Subtype.val hxy

/-- The intersection matrix of a numerical type is symmetric. -/
private theorem intersectionMatrix_isSymm (T : NumericalType) : (intersectionMatrix T).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [intersectionMatrix, T.intersection_symm]

/-- The off-diagonal entries of the intersection matrix are nonnegative. -/
private theorem intersectionMatrix_nonneg_of_ne (T : NumericalType) {i j : Fin T.componentCount}
    (hij : i ≠ j) : 0 ≤ intersectionMatrix T i j := by
  simpa [intersectionMatrix] using T.intersection_nonneg j i hij.symm

/-- The multiplicity vector lies in the kernel of the intersection matrix. -/
private theorem intersectionMatrix_mulVec_multiplicity (T : NumericalType) :
    (intersectionMatrix T).mulVec T.multiplicity = 0 := by
  ext i
  show ∑ j, intersectionMatrix T i j * T.multiplicity j = 0
  simpa [intersectionMatrix, T.intersection_symm] using T.intersection_mul_multiplicity i

/-- The intersection matrix of a numerical type is connected: no proper nonempty set of
components is orthogonal to its complement. -/
private theorem intersectionMatrix_not_forall_eq_zero (T : NumericalType)
    {I : Set (Fin T.componentCount)} (hI : I.Nonempty) (hIU : I ≠ Set.univ) :
    ¬ ∀ i ∈ I, ∀ j ∉ I, intersectionMatrix T i j = 0 := by
  intro hzero
  apply T.connected ⟨I, hI, hIU, ?_⟩
  intro i hi j hj
  simpa [intersectionMatrix, T.intersection_symm] using hzero i hi j hj

/-- The pairs `i < j` with a positive entry of the intersection matrix are the edges. -/
private theorem card_filter_intersectionMatrix_pos (T : NumericalType) :
    (univ.filter fun p : Fin T.componentCount × Fin T.componentCount =>
      p.1 < p.2 ∧ 0 < intersectionMatrix T p.1 p.2).card = edgeCount T := by
  simp [edgeCount, T.intersection_symm]

/-- **The `ℓ`-torsion of the Picard group of a numerical type is bounded by its topological
genus** as soon as the prime `ℓ` is prime to every positive intersection number and to every
multiplicity: `dim_{F_ℓ} Pic(T)[ℓ] + n ≤ 1 + e` for `n` components and `e` edges. This is Tag
0C6X for the intersection matrix, read through the embedding of Tag 0CE7 of the Picard group
into the cokernel of the intersection matrix. -/
theorem finrank_torsionBy_picardGroup_add_componentCount_le (T : NumericalType) (ℓ : ℕ)
    [Fact ℓ.Prime]
    (hℓA : ∀ i j, 0 < T.intersection i j → IsCoprime (ℓ : ℤ) (T.intersection i j))
    (hℓm : ∀ i, IsCoprime (ℓ : ℤ) (T.multiplicity i)) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) +
      T.componentCount ≤ 1 + edgeCount T := by
  classical
  have hℓA' : ∀ i j, 0 < intersectionMatrix T i j →
      IsCoprime (ℓ : ℤ) (intersectionMatrix T i j) := by
    intro i j hij
    simpa [intersectionMatrix] using hℓA j i (by simpa [intersectionMatrix] using hij)
  have hmat := Matrix.finrank_torsionBy_matrixCokernel_le_cycleRank
    (intersectionMatrix_isSymm T) (fun _ _ => intersectionMatrix_nonneg_of_ne T)
    T.multiplicity_pos (intersectionMatrix_mulVec_multiplicity T)
    (fun _ => intersectionMatrix_not_forall_eq_zero T) hℓA' hℓm
  rw [card_filter_intersectionMatrix_pos] at hmat
  let C := (Fin T.componentCount → ℤ) ⧸ LinearMap.range (intersectionMatrix T).mulVecLin
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  obtain ⟨f, hf⟩ := picardGroup_embeds_intersectionCokernel T
  let e := Submodule.quotEquivOfEq (LinearMap.range (intersectionMap T))
    (LinearMap.range (intersectionMatrix T).mulVecLin) (by congr 1)
  have hmono : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) :=
    finrank_torsionBy_le_of_injective ℓ (e.toAddEquiv.toAddMonoidHom.comp f)
      (e.injective.comp hf)
  have hmat' : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) +
      T.componentCount ≤ 1 + edgeCount T := by
    simpa [C] using hmat
  omega

/-- In case (A) of Section 0CEG the `ℓ`-torsion of the Picard group vanishes: if the
intersection graph of a numerical type has at most `n - 1` edges for `n` components, and the
prime `ℓ` is prime to every positive intersection number and every multiplicity, then
`Pic(T)[ℓ] = 0`. -/
theorem torsionBy_picardGroup_eq_bot (T : NumericalType) (ℓ : ℕ) [Fact ℓ.Prime]
    (hedge : edgeCount T + 1 ≤ T.componentCount)
    (hℓA : ∀ i j, 0 < T.intersection i j → IsCoprime (ℓ : ℤ) (T.intersection i j))
    (hℓm : ∀ i, IsCoprime (ℓ : ℤ) (T.multiplicity i)) :
    Submodule.torsionBy ℤ (picardGroup T) (ℓ : ℤ) = ⊥ := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have h := finrank_torsionBy_picardGroup_add_componentCount_le T ℓ hℓA hℓm
  have h0 : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) = 0 := by
    omega
  have hfin : Finite (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    finite_torsionBy_int (by exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero)
  have : Module.Finite (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    Module.Finite.of_finite
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  simpa using congrArg Subtype.val ((Module.finrank_zero_iff.mp h0).elim ⟨x, hx⟩ 0)

end AlgebraicGeometry.NumericalType
