module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneCycle
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkSystem

/-!
# The classification of chains of minus-two indices

A minimal numerical type of genus one each of whose components meets at most two others is a
cycle or a chain. The cycle is case (25) of the source's list and is settled in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneCycle.lean`; this file settles the chain, which
for six or more components is one of the three families (26), (27) and (28), and so completes
the classification under the hypothesis that no component meets three others.

The chain is produced by `AlgebraicGeometry.NumericalType.exists_path_ordering`. Its weights are
constant along the interior, and at each end the weight is that constant, twice it, or half it.
With the weights known the intersection matrix is too, since the intersection number of two
consecutive components is the larger of their weights; the balance relation then becomes a
three-term recurrence, linear along the interior. Solving it from each end and matching in the
middle forces the interior multiplicities to be constant and rules out an end weight equal to
the interior weight, leaving exactly three realisable pairs of end weights: both twice the
interior weight (case (28)), one half and one twice (case (26)), and both half (case (27)).

The argument is the one used for the cycle. Five consecutive components of the chain are a
*proper* chain, so the classification of proper five-chains applies: up to reordering they are
of type `A₅`, `C₅` or `B₅`, and in the last two cases the one component whose weight differs
sits at an end of the window. Hence the three interior weights of any five-window agree, and
since consecutive interior positions always lie together inside the interior of some window, all
the interior weights agree. Applying the same window at the two extreme positions reads off the
two end weights against that constant.

## Main results

* `AlgebraicGeometry.NumericalType.weight_structure_of_path` — the weights along a chain of at
  least six minus-two indices are constant on the interior, and each end weight is that
  constant, twice it, or half it.
* `AlgebraicGeometry.NumericalType.intersection_eq_max_weight_of_path` — the intersection
  number of two consecutive components of a chain is the larger of their weights, so the two
  results together determine the whole intersection matrix from the interior weight and the two
  end weights.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_neighborCount_le_two` — the
  classification for a numerical type with at least six components, none of which meets three
  others: cases (25), (26), (27) and (28).

## Implementation notes

Six or more components and exactly five are treated separately, and must be. From six on, the
interior weights are pinned down by the classification of proper five-chains, which needs a
five-window to be a *proper* subset. With five components there is no room for one, and the
conclusion genuinely fails there: cases (17) and (18) of the source's list are chains on five
components whose interior weights are *not* constant, `(1, 1, 1, 2, 2)` and `(2, 2, 2, 1, 1)`.
Five components are therefore done from four-windows. Each four-window has at most one unequal
adjacent pair and all its weights lie in a factor-two pair, so the unequal pairs of a
five-chain are none, one of the four, or the two outer ones; that leaves thirteen weight
patterns, of which the balance relations kill eight and realise five — cases (17) to (21), four
of them through the reversed ordering of a case already treated.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-- A window of consecutive components of a chain consists of distinct components which meet
exactly when their positions in the window are adjacent. -/
private lemma path_window_data (T : NumericalType) {t : ℕ}
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (base : ℕ) (hbase : base + t ≤ T.componentCount) :
    ∃ wnd : Fin t → Fin T.componentCount,
      (∀ p : Fin t, (wnd p).val = base + p.val) ∧
      Function.Injective (fun p => v (wnd p)) ∧
      (∀ p q : Fin t, T.intersection (v (wnd p)) (v (wnd q)) ≠ 0 ↔
        (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val)) := by
  obtain ⟨wnd, hwndval⟩ : ∃ wnd : Fin t → Fin T.componentCount,
      ∀ p : Fin t, (wnd p).val = base + p.val :=
    ⟨fun p => ⟨base + p.val, by have := p.isLt; omega⟩, fun p => rfl⟩
  refine ⟨wnd, hwndval, ?_, ?_⟩
  · intro p q h
    have hv : (wnd p).val = (wnd q).val := congrArg Fin.val (hvinj h)
    rw [hwndval p, hwndval q] at hv
    exact Fin.ext (by omega)
  · intro p q
    have hp := p.isLt
    have hq := q.isLt
    have hvp := hwndval p
    have hvq := hwndval q
    rw [hchar]
    simp only [Fin.ext_iff]
    omega

/-- On each window of five consecutive components of a chain of minus-two indices, the three
middle weights agree and each end weight is that weight, twice it, or half it. -/
private lemma weight_window_of_path (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (base : ℕ) (hbase : base + 4 < T.componentCount) :
    ∃ W : ℤ, 0 < W ∧
      (∀ a : Fin T.componentCount, base + 1 ≤ a.val → a.val ≤ base + 3 →
        T.weight (v a) = W) ∧
      (∀ a : Fin T.componentCount, a.val = base →
        (T.weight (v a) = W ∨ T.weight (v a) = 2 * W ∨ 2 * T.weight (v a) = W)) ∧
      (∀ a : Fin T.componentCount, a.val = base + 4 →
        (T.weight (v a) = W ∨ T.weight (v a) = 2 * W ∨ 2 * T.weight (v a) = W)) := by
  obtain ⟨wnd, hwndval, hwinj, hwadj⟩ :=
    path_window_data T (t := 5) v hvinj hchar base (by omega)
  obtain ⟨W, hWpos, hWmid, hW0, hW4⟩ := weight_interior_eq_of_five_window T (by omega)
    (fun p => v (wnd p)) hwinj (fun p => hminus _) hwadj
  obtain ⟨p0, hp0⟩ : ∃ p : Fin 5, p.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ p : Fin 5, p.val = 4 := ⟨⟨4, by omega⟩, rfl⟩
  have hzero : (0 : Fin 5) = p0 := Fin.ext (by simpa using hp0.symm)
  have hfour : (4 : Fin 5) = p4 := Fin.ext (by simpa using hp4.symm)
  refine ⟨W, hWpos, ?_, ?_, ?_⟩
  · intro a hlo hhi
    obtain ⟨p, hp⟩ : ∃ p : Fin 5, p.val = a.val - base := ⟨⟨a.val - base, by omega⟩, rfl⟩
    rw [show a = wnd p from Fin.ext (by rw [hwndval p]; omega)]
    exact hWmid p (by omega) (by omega)
  · intro a ha
    have hae : a = wnd p0 := Fin.ext (by rw [hwndval p0]; omega)
    rw [hae, ← hzero]
    exact hW0
  · intro a ha
    have hae : a = wnd p4 := Fin.ext (by rw [hwndval p4]; omega)
    rw [hae, ← hfour]
    exact hW4

/-- A property of the interior positions of a chain holds throughout the interior once it holds at
position one and passes from each interior position to the next. -/
private lemma interior_forall_of_step {n : ℕ} {P : Fin n → Prop} {a1 : Fin n} (h1 : a1.val = 1)
    (hP1 : P a1)
    (hstep : ∀ a b : Fin n, 1 ≤ a.val → b.val = a.val + 1 → b.val + 1 < n → P a → P b) :
    ∀ b : Fin n, 1 ≤ b.val → b.val + 1 < n → P b := by
  suffices key : ∀ (j : ℕ) (b : Fin n), b.val = j → 1 ≤ j → j + 1 < n → P b from
    fun b hlo hhi => key _ b rfl hlo hhi
  intro j
  induction j with
  | zero => intro b hb hj1 hj2; omega
  | succ i ih =>
      intro b hb hj1 hj2
      by_cases hi0 : i = 0
      · rwa [show b = a1 from Fin.ext (by omega)]
      · obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val = i := ⟨⟨i, by omega⟩, rfl⟩
        exact hstep a b (by omega) (by omega) (by omega) (ih a ha (by omega) (by omega))

/-- The weights along a chain of at least six minus-two indices are constant on the interior of
the chain, and the weight at each end is that constant, twice it, or half it. -/
public lemma weight_structure_of_path (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) :
    ∃ c : ℤ, 0 < c ∧
      (∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
        T.weight (v a) = c) ∧
      (∀ a : Fin T.componentCount, a.val = 0 →
        (T.weight (v a) = c ∨ T.weight (v a) = 2 * c ∨ 2 * T.weight (v a) = c)) ∧
      (∀ a : Fin T.componentCount, a.val + 1 = T.componentCount →
        (T.weight (v a) = c ∨ T.weight (v a) = 2 * c ∨ 2 * T.weight (v a) = c)) := by
  classical
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin T.componentCount, i1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hwin := weight_window_of_path T hn hminus v hvinj hchar
  -- the interior weights all agree
  obtain ⟨c0, hc0pos, hc0mid, hc0left, -⟩ := hwin 0 (by omega)
  have hall := interior_forall_of_step (P := fun a => T.weight (v a) = c0) hi1
    (hc0mid i1 (by omega) (by omega)) fun a b ha hb hbn hP => by
    obtain ⟨W, -, hWmid, -, -⟩ := hwin (a.val - 2) (by omega)
    exact (hWmid b (by omega) (by omega)).trans ((hWmid a (by omega) (by omega)).symm.trans hP)
  refine ⟨c0, hc0pos, hall, hc0left, ?_⟩
  intro a ha
  obtain ⟨W, -, hWmid, -, hWright⟩ := hwin (T.componentCount - 5) (by omega)
  obtain ⟨b, hb⟩ : ∃ b : Fin T.componentCount, b.val = T.componentCount - 2 :=
    ⟨⟨T.componentCount - 2, by omega⟩, rfl⟩
  have hWc : W = c0 :=
    (hWmid b (by omega) (by omega)).symm.trans (hall b (by omega) (by omega))
  rw [← hWc]
  exact hWright a (by omega)

/-- Along a chain of minus-two indices the intersection number of two consecutive components is
the larger of their two weights, and all other intersection numbers vanish. Together with
`AlgebraicGeometry.NumericalType.weight_structure_of_path` this determines the whole
intersection matrix of a chain from the interior weight and the two end weights. -/
public lemma intersection_eq_max_weight_of_path (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (a b : Fin T.componentCount) (hab : a.val + 1 = b.val) :
    T.intersection (v a) (v b) = max (T.weight (v a)) (T.weight (v b)) := by
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hvne : v a ≠ v b := hvinj.ne hne
  have hnz : T.intersection (v a) (v b) ≠ 0 := (hchar a b).mpr (Or.inl hab)
  have hpos : 0 < T.intersection (v a) (v b) :=
    lt_of_le_of_ne (T.intersection_nonneg _ _ hvne) (Ne.symm hnz)
  exact intersection_eq_max_weight_of_intersects T (by omega) _ _ (hminus _) (hminus _) hpos

/-! ### The balance relations along a chain -/

/-- The balance relation at a component of a chain, restricted to the positions that can
contribute. -/
private lemma path_row (T : NumericalType)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (a : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (hS : ∀ b, b ∈ S ↔ (b.val + 1 = a.val ∨ a.val + 1 = b.val ∨ b = a)) :
    ∑ b ∈ S, T.intersection (v a) (v b) * T.multiplicity (v b) = 0 := by
  classical
  have hbij : Function.Bijective v := ⟨hvinj, Finite.injective_iff_surjective.mp hvinj⟩
  have htot : ∑ b : Fin T.componentCount,
      T.intersection (v a) (v b) * T.multiplicity (v b) = 0 := by
    rw [Fintype.sum_bijective v hbij (fun b => T.intersection (v a) (v b) * T.multiplicity (v b))
      (fun j => T.intersection (v a) j * T.multiplicity j) (fun b => rfl)]
    exact T.intersection_mul_multiplicity (v a)
  rw [Finset.sum_subset (Finset.subset_univ S) ?_]
  · exact htot
  · intro x _ hxS
    have hz : T.intersection (v a) (v x) = 0 := by
      by_contra hcon
      refine hxS ((hS x).mpr ?_)
      rcases (hchar a x).mp hcon with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
    rw [hz, zero_mul]

/-- The balance relation at an interior position of a chain. -/
private lemma chain_row_interior (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (a am ap : Fin T.componentCount) (ham : am.val + 1 = a.val) (hap : a.val + 1 = ap.val) :
    max (T.weight (v am)) (T.weight (v a)) * T.multiplicity (v am)
      - 2 * T.weight (v a) * T.multiplicity (v a)
      + max (T.weight (v a)) (T.weight (v ap)) * T.multiplicity (v ap) = 0 := by
  classical
  have hama : am ≠ a := fun h => by rw [h] at ham; omega
  have hapa : ap ≠ a := fun h => by rw [h] at hap; omega
  have hamap : am ≠ ap := fun h => by rw [h] at ham; omega
  have hsum := path_row T v hvinj hchar a {am, a, ap} (by
    intro b
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega)
  rw [Finset.sum_insert (by simp [hama, hamap]), Finset.sum_insert (by simp [Ne.symm hapa]),
    Finset.sum_singleton] at hsum
  have he1 : T.intersection (v a) (v am) = max (T.weight (v am)) (T.weight (v a)) := by
    rw [T.intersection_symm]
    exact intersection_eq_max_weight_of_path T hn hminus v hvinj hchar am a ham
  have he2 : T.intersection (v a) (v ap) = max (T.weight (v a)) (T.weight (v ap)) :=
    intersection_eq_max_weight_of_path T hn hminus v hvinj hchar a ap hap
  rw [he1, he2, (hminus (v a)).2] at hsum
  linarith

/-- The balance relation at the first position of a chain. -/
private lemma chain_row_first (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (a ap : Fin T.componentCount) (ha0 : a.val = 0) (hap : a.val + 1 = ap.val) :
    2 * T.weight (v a) * T.multiplicity (v a)
      = max (T.weight (v a)) (T.weight (v ap)) * T.multiplicity (v ap) := by
  classical
  have hapa : ap ≠ a := fun h => by rw [h] at hap; omega
  have hsum := path_row T v hvinj hchar a {a, ap} (by
    intro b
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega)
  rw [Finset.sum_insert (by simp [Ne.symm hapa]), Finset.sum_singleton] at hsum
  have he2 : T.intersection (v a) (v ap) = max (T.weight (v a)) (T.weight (v ap)) :=
    intersection_eq_max_weight_of_path T hn hminus v hvinj hchar a ap hap
  rw [he2, (hminus (v a)).2] at hsum
  linarith

/-- The balance relation at the last position of a chain. -/
private lemma chain_row_last (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (a am : Fin T.componentCount) (ha : a.val + 1 = T.componentCount)
    (ham : am.val + 1 = a.val) :
    2 * T.weight (v a) * T.multiplicity (v a)
      = max (T.weight (v am)) (T.weight (v a)) * T.multiplicity (v am) := by
  classical
  have hama : am ≠ a := fun h => by rw [h] at ham; omega
  have hsum := path_row T v hvinj hchar a {am, a} (by
    intro b
    have := b.isLt
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega)
  rw [Finset.sum_insert (by simp [hama]), Finset.sum_singleton] at hsum
  have he1 : T.intersection (v a) (v am) = max (T.weight (v am)) (T.weight (v a)) := by
    rw [T.intersection_symm]
    exact intersection_eq_max_weight_of_path T hn hminus v hvinj hchar am a ham
  rw [he1, (hminus (v a)).2] at hsum
  linarith

/-! ### Multiplicities along the interior of a chain -/

/-- The successive differences of the multiplicities along the interior of a chain of at least
six minus-two indices all agree: the interior balance relation is a three-term recurrence with
constant coefficients. -/
private lemma chain_diff_const (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (c : ℤ) (hc : 0 < c)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (a1 a2 : Fin T.componentCount) (h1 : a1.val = 1) (h2 : a2.val = 2) :
    ∀ (j : ℕ) (b b' : Fin T.componentCount), b.val = j → b'.val = j + 1 → 1 ≤ j →
      j + 2 < T.componentCount →
      T.multiplicity (v b') - T.multiplicity (v b)
        = T.multiplicity (v a2) - T.multiplicity (v a1) := by
  intro j b b' hb hb' hj1 hj2
  refine interior_forall_of_step
    (P := fun b => ∀ b' : Fin T.componentCount, b'.val = b.val + 1 →
      b'.val + 1 < T.componentCount → T.multiplicity (v b') - T.multiplicity (v b)
        = T.multiplicity (v a2) - T.multiplicity (v a1)) h1
    (fun b' hb' _ => by rw [show b' = a2 from Fin.ext (by omega)]) ?_ b (by omega) (by omega) b'
    (by omega) (by omega)
  intro a b ha hb hbn hprev b' hb' hb'n
  have hrel := chain_row_interior T (by omega) hminus v hvinj hchar b a b' (by omega) (by omega)
  rw [hcint a (by omega) (by omega), hcint b (by omega) (by omega),
    hcint b' (by omega) (by omega), max_self] at hrel
  exact (mul_left_cancel₀ hc.ne' (by linarith)).trans (hprev b hb (by omega))

/-- If two successive interior multiplicities of a chain of at least six minus-two indices
agree, then all the interior multiplicities agree. -/
private lemma chain_multiplicity_const (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (c : ℤ) (hc : 0 < c)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (a1 a2 : Fin T.componentCount) (h1 : a1.val = 1) (h2 : a2.val = 2)
    (hd : T.multiplicity (v a2) = T.multiplicity (v a1)) :
    ∀ b : Fin T.componentCount, 1 ≤ b.val → b.val + 1 < T.componentCount →
      T.multiplicity (v b) = T.multiplicity (v a1) := by
  have hdiff := chain_diff_const T hn hminus v hvinj hchar c hc hcint a1 a2 h1 h2
  exact interior_forall_of_step (P := fun b => T.multiplicity (v b) = T.multiplicity (v a1)) h1 rfl
    fun a b ha hb _ hprev => by
    have := hdiff a.val a b rfl hb ha (by omega)
    omega

/-- Scaling commutes with the larger of two integers. -/
private lemma max_mul_right {x : ℤ} (hx : 0 < x) (k l : ℤ) :
    max (k * x) (l * x) = max k l * x := by
  rcases le_total k l with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_right h (le_of_lt hx))]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_right h (le_of_lt hx))]

/-! ### Matching a chain against an unbounded family -/

/-- A chain whose multiplicities and weights follow the coefficient table of an unbounded family
whose edge coefficients are the larger of the two endpoint weight coefficients matches that
table. -/
private lemma matchesCoefficients_of_path (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (f : GenusOne.LongFamily) (m' w' : ℤ) (hm : 0 < m') (hw : 0 < w')
    (hmul : ∀ a : Fin T.componentCount,
      T.multiplicity (v a) = GenusOne.longMultiplicity f T.componentCount a * m')
    (hwt : ∀ a : Fin T.componentCount,
      T.weight (v a) = GenusOne.longWeight f T.componentCount a * w')
    (hedge : ∀ a b : Fin T.componentCount, a.val + 1 = b.val →
      GenusOne.longEdge f T.componentCount a.val b.val
        = max (GenusOne.longWeight f T.componentCount a)
            (GenusOne.longWeight f T.componentCount b))
    (hzero : ∀ a b : Fin T.componentCount, a.val + 1 < b.val →
      GenusOne.longEdge f T.componentCount a.val b.val = 0) :
    MatchesCoefficients T T.componentCount
      (GenusOne.longMultiplicity f T.componentCount)
      (GenusOne.longWeight f T.componentCount)
      (GenusOne.longIntersection f T.componentCount) := by
  classical
  have hadj : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      ((a.val + 1 = b.val ∨ b.val + 1 = a.val) ∨ a = b) :=
    fun a b => (hchar a b).trans or_assoc.symm
  have he : ∀ a b : Fin T.componentCount, a ≠ b → (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      GenusOne.longIntersection f T.componentCount a b
        = max (GenusOne.longWeight f T.componentCount a)
            (GenusOne.longWeight f T.componentCount b) := by
    intro a b hab h
    simp only [GenusOne.longIntersection, ite_eq_right hab]
    rcases h with h | h
    · rw [min_eq_left (by omega), max_eq_right (by omega)]
      exact hedge a b h
    · rw [min_eq_right (by omega), max_eq_left (by omega), hedge b a h]
      exact max_comm _ _
  have hz : ∀ a b : Fin T.componentCount, a ≠ b →
      ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      GenusOne.longIntersection f T.componentCount a b = 0 := by
    intro a b hab h
    push Not at h
    have hv : a.val ≠ b.val := fun hc => hab (Fin.ext hc)
    simp only [GenusOne.longIntersection, ite_eq_right hab]
    rcases Nat.lt_or_ge a.val b.val with hlt | hge
    · rw [min_eq_left (by omega), max_eq_right (by omega)]
      exact hzero a b (by omega)
    · rw [min_eq_right (by omega), max_eq_left (by omega)]
      exact hzero b a (by omega)
  exact matchesCoefficients_of_ordering T rfl v hvinj _ _ _ _ m' w' hm hw hmul hwt
    (fun i j => intersection_eq_of_adjacency T (by omega) hminus v hvinj
      (fun a b => (a.val + 1 = b.val ∨ b.val + 1 = a.val)) hadj
      (GenusOne.longWeight f T.componentCount)
      (GenusOne.longIntersection f T.componentCount) w' hw hwt
      (fun a => GenusOne.longIntersection_self f T.componentCount a) he hz i j)
    (fun i => (hminus (v i)).1)

/-- The edge coefficients of the chain families are the larger of the two endpoint weight
coefficients. -/
private lemma longEdge_eq_max {n : ℕ} (hn : 6 ≤ n) (f : GenusOne.LongFamily)
    (hf : f = .upUp ∨ f = .upDown ∨ f = .downUp) (a b : Fin n) (hab : a.val + 1 = b.val) :
    GenusOne.longEdge f n a.val b.val
      = max (GenusOne.longWeight f n a) (GenusOne.longWeight f n b) := by
  have ha := a.isLt
  have hb := b.isLt
  rcases hf with rfl | rfl | rfl <;>
    simp only [GenusOne.longEdge, GenusOne.longWeight] <;> split_ifs <;> omega

/-- The edge coefficients of the chain families vanish on non-consecutive positions. -/
private lemma longEdge_eq_zero {n : ℕ} (f : GenusOne.LongFamily)
    (hf : f = .upUp ∨ f = .upDown ∨ f = .downUp) (a b : Fin n) (hab : a.val + 1 < b.val) :
    GenusOne.longEdge f n a.val b.val = 0 := by
  rcases hf with rfl | rfl | rfl <;>
    simp only [GenusOne.longEdge] <;> split_ifs <;> omega

/-- Reversing a chain ordering again gives a chain ordering. -/
private lemma path_reverse (T : NumericalType)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) :
    ∃ rev : Fin T.componentCount → Fin T.componentCount,
      (∀ a, (rev a).val = T.componentCount - 1 - a.val) ∧
      Function.Injective (fun a => v (rev a)) ∧
      (∀ a b : Fin T.componentCount, T.intersection (v (rev a)) (v (rev b)) ≠ 0 ↔
        (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) := by
  obtain ⟨rev, hrev⟩ : ∃ rev : Fin T.componentCount → Fin T.componentCount,
      ∀ a, (rev a).val = T.componentCount - 1 - a.val :=
    ⟨fun a => ⟨T.componentCount - 1 - a.val, by have := a.isLt; omega⟩, fun a => rfl⟩
  refine ⟨rev, hrev, ?_, ?_⟩
  · intro a b h
    have h2 : (rev a).val = (rev b).val := congrArg Fin.val (hvinj h)
    rw [hrev a, hrev b] at h2
    have ha := a.isLt
    have hb := b.isLt
    exact Fin.ext (by omega)
  · intro a b
    have ha := a.isLt
    have hb := b.isLt
    have hra := hrev a
    have hrb := hrev b
    rw [hchar]
    simp only [Fin.ext_iff]
    omega

/-! ### Weights along a chain of five minus-two indices -/

/-- Two weights drawn from a factor-two pair differ by a factor of one or two. -/
private lemma step_of_mem {W x y : ℤ} (hW : 0 < W) (hx : x = W ∨ x = 2 * W)
    (hy : y = W ∨ y = 2 * W) : y = x ∨ y = 2 * x ∨ 2 * y = x := by
  omega

/-- Two overlapping four-windows, each with at most one unequal adjacent pair, leave at most one
unequal pair among the first three and at most one among the last three. -/
private lemma pattern_of_windows {a b c d e : ℤ}
    (h0 : (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d))
    (h1 : (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨ (b = c ∧ d = e)) :
    (b = c ∧ c = d ∧ d = e) ∨ (a = b ∧ c = d ∧ d = e) ∨ (a = b ∧ b = c ∧ d = e) ∨
      (a = b ∧ b = c ∧ c = d) ∨ (b = c ∧ c = d) := by
  omega

/-- The weights along a chain of exactly five minus-two indices. Each adjacent pair differs by a
factor of one or two, and the pairs that differ are confined by the two four-windows: at most one
of the first three pairs differs, and at most one of the last three, so the differing pairs are
none, one of the four, or the two outer ones. -/
private lemma five_chain_weight_steps (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4) :
    (T.weight (v j1) = T.weight (v j0) ∨ T.weight (v j1) = 2 * T.weight (v j0) ∨
        2 * T.weight (v j1) = T.weight (v j0)) ∧
      (T.weight (v j2) = T.weight (v j1) ∨ T.weight (v j2) = 2 * T.weight (v j1) ∨
        2 * T.weight (v j2) = T.weight (v j1)) ∧
      (T.weight (v j3) = T.weight (v j2) ∨ T.weight (v j3) = 2 * T.weight (v j2) ∨
        2 * T.weight (v j3) = T.weight (v j2)) ∧
      (T.weight (v j4) = T.weight (v j3) ∨ T.weight (v j4) = 2 * T.weight (v j3) ∨
        2 * T.weight (v j4) = T.weight (v j3)) ∧
      ((T.weight (v j1) = T.weight (v j2) ∧ T.weight (v j2) = T.weight (v j3) ∧
            T.weight (v j3) = T.weight (v j4)) ∨
        (T.weight (v j0) = T.weight (v j1) ∧ T.weight (v j2) = T.weight (v j3) ∧
            T.weight (v j3) = T.weight (v j4)) ∨
        (T.weight (v j0) = T.weight (v j1) ∧ T.weight (v j1) = T.weight (v j2) ∧
            T.weight (v j3) = T.weight (v j4)) ∨
        (T.weight (v j0) = T.weight (v j1) ∧ T.weight (v j1) = T.weight (v j2) ∧
            T.weight (v j2) = T.weight (v j3)) ∨
        (T.weight (v j1) = T.weight (v j2) ∧ T.weight (v j2) = T.weight (v j3))) := by
  classical
  have f0 : (0 : Fin 4).val = 0 := by decide
  have f1 : (1 : Fin 4).val = 1 := by decide
  have f2 : (2 : Fin 4).val = 2 := by decide
  have f3 : (3 : Fin 4).val = 3 := by decide
  obtain ⟨u, hu, hui, hua⟩ := path_window_data T (t := 4) v hvinj hchar 0 (by omega)
  obtain ⟨W, hW, hmemW, hpatW⟩ := weight_pattern_of_four_window T (by omega)
    (fun p => v (u p)) hui (fun p => hminus _) hua
  obtain ⟨z, hz, hzi, hza⟩ := path_window_data T (t := 4) v hvinj hchar 1 (by omega)
  obtain ⟨V, hV, hmemV, hpatV⟩ := weight_pattern_of_four_window T (by omega)
    (fun p => v (z p)) hzi (fun p => hminus _) hza
  have hu0 : u 0 = j0 := Fin.ext (by rw [hu 0]; omega)
  have hu1 : u 1 = j1 := Fin.ext (by rw [hu 1]; omega)
  have hu2 : u 2 = j2 := Fin.ext (by rw [hu 2]; omega)
  have hu3 : u 3 = j3 := Fin.ext (by rw [hu 3]; omega)
  have hz0 : z 0 = j1 := Fin.ext (by rw [hz 0]; omega)
  have hz1 : z 1 = j2 := Fin.ext (by rw [hz 1]; omega)
  have hz2 : z 2 = j3 := Fin.ext (by rw [hz 2]; omega)
  have hz3 : z 3 = j4 := Fin.ext (by rw [hz 3]; omega)
  have m0 := hmemW 0
  have m1 := hmemW 1
  have m2 := hmemW 2
  have m3 := hmemW 3
  have n3 := hmemV 2
  have n4 := hmemV 3
  simp only [hu0, hu1, hu2, hu3, hz0, hz1, hz2, hz3] at m0 m1 m2 m3 n3 n4 hpatW hpatV
  exact ⟨step_of_mem hW m0 m1, step_of_mem hW m1 m2, step_of_mem hW m2 m3,
    step_of_mem hV n3 n4, pattern_of_windows hpatW hpatV⟩

/-- The five balance relations of a chain of five minus-two indices whose weights are given
multiples of a common positive integer, divided through by that integer. -/
private lemma five_rows (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (x : ℤ) (hx : 0 < x) (k0 k1 k2 k3 k4 : ℤ)
    (hw0 : T.weight (v j0) = k0 * x) (hw1 : T.weight (v j1) = k1 * x)
    (hw2 : T.weight (v j2) = k2 * x) (hw3 : T.weight (v j3) = k3 * x)
    (hw4 : T.weight (v j4) = k4 * x) :
    2 * k0 * T.multiplicity (v j0) - max k0 k1 * T.multiplicity (v j1) = 0 ∧
      max k0 k1 * T.multiplicity (v j0) - 2 * k1 * T.multiplicity (v j1)
        + max k1 k2 * T.multiplicity (v j2) = 0 ∧
      max k1 k2 * T.multiplicity (v j1) - 2 * k2 * T.multiplicity (v j2)
        + max k2 k3 * T.multiplicity (v j3) = 0 ∧
      max k2 k3 * T.multiplicity (v j2) - 2 * k3 * T.multiplicity (v j3)
        + max k3 k4 * T.multiplicity (v j4) = 0 ∧
      2 * k4 * T.multiplicity (v j4) - max k3 k4 * T.multiplicity (v j3) = 0 := by
  have hr0 := chain_row_first T (by omega) hminus v hvinj hchar j0 j1 hj0 (by omega)
  have hr1 := chain_row_interior T (by omega) hminus v hvinj hchar j1 j0 j2 (by omega) (by omega)
  have hr2 := chain_row_interior T (by omega) hminus v hvinj hchar j2 j1 j3 (by omega) (by omega)
  have hr3 := chain_row_interior T (by omega) hminus v hvinj hchar j3 j2 j4 (by omega) (by omega)
  have hr4 := chain_row_last T (by omega) hminus v hvinj hchar j4 j3 (by omega) (by omega)
  simp only [hw0, hw1, hw2, hw3, hw4, max_mul_right hx] at hr0 hr1 hr2 hr3 hr4
  have hxc : ∀ y : ℤ, x * y = 0 → y = 0 := fun y h =>
    (mul_eq_zero.mp h).resolve_left (ne_of_gt hx)
  exact ⟨hxc _ (by linarith), hxc _ (by linarith), hxc _ (by linarith), hxc _ (by linarith),
    hxc _ (by linarith)⟩

/-! ### Matching a five-component chain against a finite table -/

/-- A chain of five components whose multiplicities and weights follow a finite coefficient
table whose diagonal is minus twice the weight, whose consecutive entries are the larger of the
two endpoint weights and whose remaining entries vanish, matches that table. -/
private lemma matchesFinite_five (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (mc wc : List ℤ) (ac : List (List ℤ)) (hlen : mc.length = 5)
    (m' w' : ℤ) (hm : 0 < m') (hw : 0 < w')
    (hmul : ∀ a : Fin T.componentCount, T.multiplicity (v a) = mc.getD a.val 0 * m')
    (hwt : ∀ a : Fin T.componentCount, T.weight (v a) = wc.getD a.val 0 * w')
    (hdiag : ∀ k, k < 5 → (ac.getD k []).getD k 0 = -2 * wc.getD k 0)
    (hedgeL : ∀ k, k + 1 < 5 →
      (ac.getD k []).getD (k + 1) 0 = max (wc.getD k 0) (wc.getD (k + 1) 0))
    (hedgeR : ∀ k, k + 1 < 5 →
      (ac.getD (k + 1) []).getD k 0 = max (wc.getD k 0) (wc.getD (k + 1) 0))
    (hzerL : ∀ k l, k + 1 < l → l < 5 → (ac.getD k []).getD l 0 = 0)
    (hzerR : ∀ k l, k + 1 < l → l < 5 → (ac.getD l []).getD k 0 = 0) :
    MatchesFinite T mc wc ac := by
  refine matchesFinite_of_adjacency T (by omega) rfl hminus v hvinj
    (fun a b => a.val + 1 = b.val ∨ b.val + 1 = a.val) ?_ mc wc ac (by omega) m' w' hm hw
    hmul hwt (fun a => hdiag a.val (by omega)) ?_ ?_
  · exact fun a b => (hchar a b).trans or_assoc.symm
  · intro a b hab hadj
    have hal := a.isLt
    have hbl := b.isLt
    rcases hadj with h | h
    · rw [show b.val = a.val + 1 from h.symm]
      exact hedgeL a.val (by omega)
    · rw [show a.val = b.val + 1 from h.symm, hedgeR b.val (by omega)]
      exact max_comm _ _
  · intro a b hab hadj
    have hal := a.isLt
    have hbl := b.isLt
    have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    push Not at hadj
    rcases Nat.lt_or_ge a.val b.val with hlt | hge
    · exact hzerL a.val b.val (by omega) (by omega)
    · exact hzerR b.val a.val (by omega) (by omega)

/-- A property of the positions of a chain of five components holds everywhere once it holds at
each of the five positions. -/
private lemma forall_of_five {n : ℕ} (h5 : n = 5) {P : Fin n → Prop} {j0 j1 j2 j3 j4 : Fin n}
    (hj0 : j0.val = 0) (hj1 : j1.val = 1) (hj2 : j2.val = 2) (hj3 : j3.val = 3)
    (hj4 : j4.val = 4) (p0 : P j0) (p1 : P j1) (p2 : P j2) (p3 : P j3) (p4 : P j4)
    (a : Fin n) : P a := by
  have ha := a.isLt
  obtain h | h | h | h | h : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 := by
    omega
  · rwa [show a = j0 from Fin.ext (by omega)]
  · rwa [show a = j1 from Fin.ext (by omega)]
  · rwa [show a = j2 from Fin.ext (by omega)]
  · rwa [show a = j3 from Fin.ext (by omega)]
  · rwa [show a = j4 from Fin.ext (by omega)]

/-- A chain of five components whose multiplicities and weights are given at each position by a
listed finite coefficient table, whose diagonal is minus twice the weight, whose consecutive
entries are the larger of the two endpoint weights and whose remaining entries vanish, is a genus
one configuration. -/
private lemma isGenusOneConfiguration_of_five_values (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (mc wc : List ℤ) (ac : List (List ℤ)) (hpat : (mc, wc, ac) ∈ GenusOne.finitePatterns)
    (hlen : mc.length = 5) (m' w' : ℤ) (hm : 0 < m') (hw : 0 < w')
    (htab : (∀ k, k < 5 → (ac.getD k []).getD k 0 = -2 * wc.getD k 0) ∧
      (∀ k, k < 4 → (ac.getD k []).getD (k + 1) 0 = max (wc.getD k 0) (wc.getD (k + 1) 0) ∧
        (ac.getD (k + 1) []).getD k 0 = max (wc.getD k 0) (wc.getD (k + 1) 0)) ∧
      (∀ l, l < 5 → ∀ k, k < l - 1 →
        (ac.getD k []).getD l 0 = 0 ∧ (ac.getD l []).getD k 0 = 0))
    (hm0 : T.multiplicity (v j0) = mc.getD 0 0 * m')
    (hm1 : T.multiplicity (v j1) = mc.getD 1 0 * m')
    (hm2 : T.multiplicity (v j2) = mc.getD 2 0 * m')
    (hm3 : T.multiplicity (v j3) = mc.getD 3 0 * m')
    (hm4 : T.multiplicity (v j4) = mc.getD 4 0 * m')
    (hw0 : T.weight (v j0) = wc.getD 0 0 * w') (hw1 : T.weight (v j1) = wc.getD 1 0 * w')
    (hw2 : T.weight (v j2) = wc.getD 2 0 * w') (hw3 : T.weight (v j3) = wc.getD 3 0 * w')
    (hw4 : T.weight (v j4) = wc.getD 4 0 * w') :
    IsGenusOneConfiguration T :=
  Or.inr <| Or.inl <| ⟨(mc, wc, ac), hpat,
    matchesFinite_five T h5 hminus v hvinj hchar mc wc ac hlen m' w' hm hw
    (forall_of_five h5 hj0 hj1 hj2 hj3 hj4 (by rwa [hj0]) (by rwa [hj1]) (by rwa [hj2])
      (by rwa [hj3]) (by rwa [hj4]))
    (forall_of_five h5 hj0 hj1 hj2 hj3 hj4 (by rwa [hj0]) (by rwa [hj1]) (by rwa [hj2])
      (by rwa [hj3]) (by rwa [hj4]))
    htab.1 (fun k hk => (htab.2.1 k (by omega)).1) (fun k hk => (htab.2.1 k (by omega)).2)
    (fun k l h1 h2 => (htab.2.2 l h2 k (by omega)).1)
    (fun k l h1 h2 => (htab.2.2 l h2 k (by omega)).2)⟩

/-- The weight pattern `(1, 1, 1, 2, 2)` on a chain of five minus-two indices is case (17). -/
private lemma five_case_17 (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hw0 : T.weight (v j0) = T.weight (v j2)) (hw1 : T.weight (v j1) = T.weight (v j2))
    (hw3 : T.weight (v j3) = 2 * T.weight (v j2))
    (hw4 : T.weight (v j4) = 2 * T.weight (v j2)) :
    IsGenusOneConfiguration T := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 (T.weight (v j2)) (T.weight_pos _) 1 1 1 2 2
    (by linarith) (by linarith) (by ring) hw3 hw4
  norm_num at q0 q1 q2 q3 q4
  have hs : T.multiplicity (v j1) = 2 * T.multiplicity (v j0) ∧
      T.multiplicity (v j2) = 3 * T.multiplicity (v j0) ∧
      T.multiplicity (v j3) = 2 * T.multiplicity (v j0) ∧
      T.multiplicity (v j4) = T.multiplicity (v j0) := by omega
  refine isGenusOneConfiguration_of_five_values T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
    [1, 2, 3, 2, 1] [1, 1, 1, 2, 2]
    [[-2, 1, 0, 0, 0], [1, -2, 1, 0, 0], [0, 1, -2, 2, 0], [0, 0, 2, -4, 2],
      [0, 0, 0, 2, -4]] (by decide) (by decide)
    (T.multiplicity (v j0)) (T.weight (v j2))
    (T.multiplicity_pos _) (T.weight_pos _) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num <;> omega

/-- The weight pattern `(2, 2, 2, 1, 1)` on a chain of five minus-two indices is case (18). -/
private lemma five_case_18 (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hw0 : T.weight (v j0) = 2 * T.weight (v j3))
    (hw1 : T.weight (v j1) = 2 * T.weight (v j3))
    (hw2 : T.weight (v j2) = 2 * T.weight (v j3))
    (hw4 : T.weight (v j4) = T.weight (v j3)) :
    IsGenusOneConfiguration T := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 (T.weight (v j3)) (T.weight_pos _) 2 2 2 1 1
    hw0 hw1 hw2 (by ring) (by linarith)
  norm_num at q0 q1 q2 q3 q4
  refine isGenusOneConfiguration_of_five_values T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
    [1, 2, 3, 4, 2] [2, 2, 2, 1, 1]
    [[-4, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 0], [0, 0, 2, -2, 1],
      [0, 0, 0, 1, -2]] (by decide) (by decide)
    (T.multiplicity (v j0)) (T.weight (v j3))
    (T.multiplicity_pos _) (T.weight_pos _) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num <;> omega

/-- The weight pattern `(1, 2, 2, 2, 4)` on a chain of five minus-two indices is case (19). -/
private lemma five_case_19 (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hw1 : T.weight (v j1) = 2 * T.weight (v j0))
    (hw2 : T.weight (v j2) = 2 * T.weight (v j0))
    (hw3 : T.weight (v j3) = 2 * T.weight (v j0))
    (hw4 : T.weight (v j4) = 4 * T.weight (v j0)) :
    IsGenusOneConfiguration T := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 (T.weight (v j0)) (T.weight_pos _) 1 2 2 2 4
    (by ring) hw1 hw2 hw3 hw4
  norm_num at q0 q1 q2 q3 q4
  refine isGenusOneConfiguration_of_five_values T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
    [2, 2, 2, 2, 1] [1, 2, 2, 2, 4]
    [[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 0], [0, 0, 2, -4, 4],
      [0, 0, 0, 4, -8]] (by decide) (by decide)
    (T.multiplicity (v j4)) (T.weight (v j0))
    (T.multiplicity_pos _) (T.weight_pos _) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num <;> omega

/-- The weight pattern `(1, 2, 2, 2, 1)` on a chain of five minus-two indices is case (20). -/
private lemma five_case_20 (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hw1 : T.weight (v j1) = 2 * T.weight (v j0))
    (hw2 : T.weight (v j2) = 2 * T.weight (v j0))
    (hw3 : T.weight (v j3) = 2 * T.weight (v j0))
    (hw4 : T.weight (v j4) = T.weight (v j0)) :
    IsGenusOneConfiguration T := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 (T.weight (v j0)) (T.weight_pos _) 1 2 2 2 1
    (by ring) hw1 hw2 hw3 (by linarith)
  norm_num at q0 q1 q2 q3 q4
  refine isGenusOneConfiguration_of_five_values T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
    [1, 1, 1, 1, 1] [1, 2, 2, 2, 1]
    [[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 0], [0, 0, 2, -4, 2],
      [0, 0, 0, 2, -2]] (by decide) (by decide)
    (T.multiplicity (v j0)) (T.weight (v j0))
    (T.multiplicity_pos _) (T.weight_pos _) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num <;> omega

/-- The weight pattern `(2, 1, 1, 1, 2)` on a chain of five minus-two indices is case (21). -/
private lemma five_case_21 (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hw0 : T.weight (v j0) = 2 * T.weight (v j1))
    (hw2 : T.weight (v j2) = T.weight (v j1))
    (hw3 : T.weight (v j3) = T.weight (v j1))
    (hw4 : T.weight (v j4) = 2 * T.weight (v j1)) :
    IsGenusOneConfiguration T := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 (T.weight (v j1)) (T.weight_pos _) 2 1 1 1 2
    hw0 (by ring) (by linarith) (by linarith) hw4
  norm_num at q0 q1 q2 q3 q4
  refine isGenusOneConfiguration_of_five_values T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
    [1, 2, 2, 2, 1] [2, 1, 1, 1, 2]
    [[-4, 2, 0, 0, 0], [2, -2, 1, 0, 0], [0, 1, -2, 1, 0], [0, 0, 1, -2, 2],
      [0, 0, 0, 2, -4]] (by decide) (by decide)
    (T.multiplicity (v j0)) (T.weight (v j1))
    (T.multiplicity_pos _) (T.weight_pos _) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num <;> omega


/-- The reversed ordering of a chain of five components exchanges the two ends and the two
positions next to them, and fixes the middle. -/
private lemma five_path_reverse (T : NumericalType) (h5 : T.componentCount = 5)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4) :
    ∃ rev : Fin T.componentCount → Fin T.componentCount,
      Function.Injective (fun a => v (rev a)) ∧
      (∀ a b : Fin T.componentCount, T.intersection (v (rev a)) (v (rev b)) ≠ 0 ↔
        (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) ∧
      v (rev j0) = v j4 ∧ v (rev j1) = v j3 ∧ v (rev j2) = v j2 ∧ v (rev j3) = v j1 ∧
      v (rev j4) = v j0 := by
  obtain ⟨rev, hrev, hrevinj, hrevchar⟩ := path_reverse T v hvinj hchar
  refine ⟨rev, hrevinj, hrevchar, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact congrArg v (Fin.ext (by rw [hrev]; omega))

/-- The weight patterns `(1, 1, 1, 1, 1)`, `(1, 2, 2, 2, 2)`, `(2, 1, 1, 1, 1)`,
`(1, 1, 1, 1, 2)` and `(2, 2, 2, 2, 1)` do not occur on a chain of five minus-two indices: their
balance relations have no positive solution. -/
private lemma five_chain_weights_absurd (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (x : ℤ) (hx : 0 < x) (k0 k1 k2 k3 k4 : ℤ)
    (hk : (k0 = 1 ∧ k1 = 1 ∧ k2 = 1 ∧ k3 = 1 ∧ k4 = 1) ∨
      (k0 = 1 ∧ k1 = 2 ∧ k2 = 2 ∧ k3 = 2 ∧ k4 = 2) ∨
      (k0 = 2 ∧ k1 = 1 ∧ k2 = 1 ∧ k3 = 1 ∧ k4 = 1) ∨
      (k0 = 1 ∧ k1 = 1 ∧ k2 = 1 ∧ k3 = 1 ∧ k4 = 2) ∨
      (k0 = 2 ∧ k1 = 2 ∧ k2 = 2 ∧ k3 = 2 ∧ k4 = 1))
    (hw0 : T.weight (v j0) = k0 * x) (hw1 : T.weight (v j1) = k1 * x)
    (hw2 : T.weight (v j2) = k2 * x) (hw3 : T.weight (v j3) = k3 * x)
    (hw4 : T.weight (v j4) = k4 * x) : False := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := five_rows T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 x hx k0 k1 k2 k3 k4 hw0 hw1 hw2 hw3 hw4
  have p0 := T.multiplicity_pos (v j0)
  have p1 := T.multiplicity_pos (v j1)
  have p2 := T.multiplicity_pos (v j2)
  have p3 := T.multiplicity_pos (v j3)
  have p4 := T.multiplicity_pos (v j4)
  rcases hk with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
    norm_num at q0 q1 q2 q3 q4 <;> omega

/-- A chain of five minus-two indices whose three middle weights agree is one of cases (19),
(20) and (21). -/
private lemma five_chain_config_outer (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (j0 j1 j2 j3 j4 : Fin T.componentCount) (hj0 : j0.val = 0) (hj1 : j1.val = 1)
    (hj2 : j2.val = 2) (hj3 : j3.val = 3) (hj4 : j4.val = 4)
    (hs0 : T.weight (v j1) = T.weight (v j0) ∨ T.weight (v j1) = 2 * T.weight (v j0) ∨
      2 * T.weight (v j1) = T.weight (v j0))
    (hs3 : T.weight (v j4) = T.weight (v j3) ∨ T.weight (v j4) = 2 * T.weight (v j3) ∨
      2 * T.weight (v j4) = T.weight (v j3))
    (f1 : T.weight (v j1) = T.weight (v j2)) (f2 : T.weight (v j2) = T.weight (v j3)) :
    IsGenusOneConfiguration T := by
  obtain ⟨rev, hrevinj, hrevchar, hq0, hq1, hq2, hq3, hq4⟩ :=
    five_path_reverse T h5 v hvinj hchar j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
  have bad := five_chain_weights_absurd T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4
  rcases hs0 with h | h | h <;> rcases hs3 with g | g | g
  · exact (bad (T.weight (v j0)) (T.weight_pos _) 1 1 1 1 1 (by norm_num) (by ring)
      (by linarith) (by linarith) (by linarith) (by linarith)).elim
  · exact (bad (T.weight (v j0)) (T.weight_pos _) 1 1 1 1 2 (by norm_num) (by ring)
      (by linarith) (by linarith) (by linarith) (by linarith)).elim
  · exact (bad (T.weight (v j4)) (T.weight_pos _) 2 2 2 2 1 (by norm_num) (by linarith)
      (by linarith) (by linarith) (by linarith) (by ring)).elim
  · exact (bad (T.weight (v j0)) (T.weight_pos _) 1 2 2 2 2 (by norm_num) (by ring)
      (by linarith) (by linarith) (by linarith) (by linarith)).elim
  · exact five_case_19 T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
      hj0 hj1 hj2 hj3 hj4 (by linarith) (by linarith) (by linarith) (by linarith)
  · exact five_case_20 T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
      hj0 hj1 hj2 hj3 hj4 (by linarith) (by linarith) (by linarith) (by linarith)
  · exact (bad (T.weight (v j1)) (T.weight_pos _) 2 1 1 1 1 (by norm_num) (by linarith)
      (by ring) (by linarith) (by linarith) (by linarith)).elim
  · exact five_case_21 T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
      hj0 hj1 hj2 hj3 hj4 (by linarith) (by linarith) (by linarith) (by linarith)
  · exact five_case_19 T h5 hminus (fun a => v (rev a)) hrevinj hrevchar
      j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
      (by rw [hq1, hq0]; linarith) (by rw [hq2, hq0]; linarith)
      (by rw [hq3, hq0]; linarith) (by rw [hq4, hq0]; linarith)

/-- **The five-component chain.** A numerical type with exactly five components, all of them
minus-two indices, whose components form a chain is one of cases (17) to (21) of the source's
list. -/
private lemma five_chain_config (T : NumericalType) (h5 : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) :
    IsGenusOneConfiguration T := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ x : Fin T.componentCount, x.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ x : Fin T.componentCount, x.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨j2, hj2⟩ : ∃ x : Fin T.componentCount, x.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨j3, hj3⟩ : ∃ x : Fin T.componentCount, x.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  obtain ⟨j4, hj4⟩ : ∃ x : Fin T.componentCount, x.val = 4 := ⟨⟨4, by omega⟩, rfl⟩
  obtain ⟨hs0, hs1, hs2, hs3, hS⟩ := five_chain_weight_steps T h5 hminus v hvinj hchar
    j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
  obtain ⟨rev, hrevinj, hrevchar, hq0, hq1, hq2, hq3, hq4⟩ :=
    five_path_reverse T h5 v hvinj hchar j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
  have outer := five_chain_config_outer T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
    hj0 hj1 hj2 hj3 hj4 hs0 hs3
  rcases hS with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨c1, c2, c3⟩ | ⟨d1, d2, d3⟩ | ⟨f1, f2⟩
  · exact outer a1 a2
  · rcases hs1 with h | h | h
    · exact outer h.symm b2
    · exact five_case_18 T h5 hminus (fun a => v (rev a)) hrevinj hrevchar
        j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
        (by rw [hq0, hq3]; linarith) (by rw [hq1, hq3]; linarith)
        (by rw [hq2, hq3]; linarith) (by rw [hq4, hq3]; linarith)
    · exact five_case_17 T h5 hminus (fun a => v (rev a)) hrevinj hrevchar
        j0 j1 j2 j3 j4 hj0 hj1 hj2 hj3 hj4
        (by rw [hq0, hq2]; linarith) (by rw [hq1, hq2]; linarith)
        (by rw [hq3, hq2]; linarith) (by rw [hq4, hq2]; linarith)
  · rcases hs2 with h | h | h
    · exact outer c2 h.symm
    · exact five_case_17 T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
        hj0 hj1 hj2 hj3 hj4 (by linarith) (by linarith) (by linarith) (by linarith)
    · exact five_case_18 T h5 hminus v hvinj hchar j0 j1 j2 j3 j4
        hj0 hj1 hj2 hj3 hj4 (by linarith) (by linarith) (by linarith) (by linarith)
  · exact outer d2 d3
  · exact outer f1 f2

/-! ### The end relations of a chain of at least six components -/

/-- The two balance relations at an end of a chain whose interior weight is `c`, solved for each
of the three possible end weights `c`, `2 * c` and `c / 2`. -/
private lemma chain_end_relation {c w : ℤ} (m₀ m₁ m₂ : ℤ) (hc : 0 < c)
    (hw : w = c ∨ w = 2 * c ∨ 2 * w = c) (h₀ : 2 * w * m₀ = max w c * m₁)
    (h₁ : max w c * m₀ - 2 * c * m₁ + c * m₂ = 0) :
    (w = c ∧ m₂ - m₁ = m₀) ∨ (w = 2 * c ∧ m₁ = 2 * m₀ ∧ m₂ = m₁) ∨
      (2 * w = c ∧ m₁ = m₀ ∧ m₂ = m₁) := by
  have hcz : ∀ x : ℤ, c * x = 0 → x = 0 := fun x h => (mul_eq_zero.mp h).resolve_left hc.ne'
  rcases hw with rfl | rfl | hw
  · rw [max_self] at h₀ h₁
    have e₁ := hcz (2 * m₀ - m₁) (by linarith)
    have e₂ := hcz (m₀ - 2 * m₁ + m₂) (by linarith)
    exact Or.inl ⟨rfl, by linarith⟩
  · rw [max_eq_left (by linarith : c ≤ 2 * c)] at h₀ h₁
    have e₁ := hcz (4 * m₀ - 2 * m₁) (by linarith)
    have e₂ := hcz (2 * m₀ - 2 * m₁ + m₂) (by linarith)
    exact Or.inr (Or.inl ⟨rfl, by linarith, by linarith⟩)
  · rw [max_eq_right (by linarith : w ≤ c)] at h₀ h₁
    rw [hw] at h₀
    have e₁ := hcz (m₀ - m₁) (by linarith)
    have e₂ := hcz (m₀ - 2 * m₁ + m₂) (by linarith)
    exact Or.inr (Or.inr ⟨hw, by linarith, by linarith⟩)

/-- The end relation at the first position of a chain of at least six minus-two indices whose
interior weight is `c`. -/
private lemma chain_left_end (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (c : ℤ) (hc : 0 < c)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (i0 i1 i2 : Fin T.componentCount) (h0 : i0.val = 0) (h1 : i1.val = 1) (h2 : i2.val = 2)
    (hw : T.weight (v i0) = c ∨ T.weight (v i0) = 2 * c ∨ 2 * T.weight (v i0) = c) :
    (T.weight (v i0) = c ∧
        T.multiplicity (v i2) - T.multiplicity (v i1) = T.multiplicity (v i0)) ∨
      (T.weight (v i0) = 2 * c ∧ T.multiplicity (v i1) = 2 * T.multiplicity (v i0) ∧
        T.multiplicity (v i2) = T.multiplicity (v i1)) ∨
      (2 * T.weight (v i0) = c ∧ T.multiplicity (v i1) = T.multiplicity (v i0) ∧
        T.multiplicity (v i2) = T.multiplicity (v i1)) := by
  have h₀ := chain_row_first T (by omega) hminus v hvinj hchar i0 i1 h0 (by omega)
  have h₁ := chain_row_interior T (by omega) hminus v hvinj hchar i1 i0 i2 (by omega) (by omega)
  rw [hcint i1 (by omega) (by omega)] at h₀
  rw [hcint i1 (by omega) (by omega), hcint i2 (by omega) (by omega), max_self] at h₁
  exact chain_end_relation _ _ _ hc hw h₀ h₁

/-- The end relation at the last position of a chain of at least six minus-two indices whose
interior weight is `c`. -/
private lemma chain_right_end (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (c : ℤ) (hc : 0 < c)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (iK iM iL : Fin T.componentCount) (hK : iK.val = T.componentCount - 3)
    (hM : iM.val = T.componentCount - 2) (hL : iL.val = T.componentCount - 1)
    (hw : T.weight (v iL) = c ∨ T.weight (v iL) = 2 * c ∨ 2 * T.weight (v iL) = c) :
    (T.weight (v iL) = c ∧
        T.multiplicity (v iK) - T.multiplicity (v iM) = T.multiplicity (v iL)) ∨
      (T.weight (v iL) = 2 * c ∧ T.multiplicity (v iM) = 2 * T.multiplicity (v iL) ∧
        T.multiplicity (v iK) = T.multiplicity (v iM)) ∨
      (2 * T.weight (v iL) = c ∧ T.multiplicity (v iM) = T.multiplicity (v iL) ∧
        T.multiplicity (v iK) = T.multiplicity (v iM)) := by
  have h₀ := chain_row_last T (by omega) hminus v hvinj hchar iL iM (by omega) (by omega)
  have h₁ := chain_row_interior T (by omega) hminus v hvinj hchar iM iK iL (by omega) (by omega)
  rw [hcint iM (by omega) (by omega), max_comm] at h₀
  rw [hcint iK (by omega) (by omega), hcint iM (by omega) (by omega), max_self, max_comm] at h₁
  exact chain_end_relation _ _ (T.multiplicity (v iK)) hc hw h₀ (by linarith)

/-! ### Realising the three chain families -/

/-- A property of the positions of a chain holds everywhere once it holds at the two ends and
along the interior. -/
private lemma forall_fin_of_ends {n : ℕ} {P : Fin n → Prop} {i0 iL : Fin n} (h0 : i0.val = 0)
    (hL : iL.val = n - 1) (hP0 : P i0) (hmid : ∀ a : Fin n, 1 ≤ a.val → a.val + 1 < n → P a)
    (hPL : P iL) (a : Fin n) : P a := by
  have ha := a.isLt
  by_cases hz : a.val = 0
  · rwa [show a = i0 from Fin.ext (by omega)]
  by_cases hl : a.val + 1 = n
  · rwa [show a = iL from Fin.ext (by omega)]
  exact hmid a (by omega) (by omega)

/-- A chain of at least six minus-two indices whose multiplicities and weights follow the
coefficient table of one of the three chain families, at both ends and along the interior, is
that family. -/
private lemma isGenusOneConfiguration_of_chain (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (f : GenusOne.LongFamily) (hf : f = .upUp ∨ f = .upDown ∨ f = .downUp) (m' w' : ℤ)
    (hm : 0 < m') (hw : 0 < w') (i0 iL : Fin T.componentCount) (h0 : i0.val = 0)
    (hL : iL.val = T.componentCount - 1)
    (hm0 : T.multiplicity (v i0) = GenusOne.longMultiplicity f T.componentCount i0 * m')
    (hmmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.multiplicity (v a) = GenusOne.longMultiplicity f T.componentCount a * m')
    (hmL : T.multiplicity (v iL) = GenusOne.longMultiplicity f T.componentCount iL * m')
    (hw0 : T.weight (v i0) = GenusOne.longWeight f T.componentCount i0 * w')
    (hwmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = GenusOne.longWeight f T.componentCount a * w')
    (hwL : T.weight (v iL) = GenusOne.longWeight f T.componentCount iL * w') :
    IsGenusOneConfiguration T :=
  Or.inr <| Or.inr ⟨T.componentCount, f, hn,
    matchesCoefficients_of_path T (by omega) hminus v hvinj hchar f m' w' hm hw
      (forall_fin_of_ends h0 hL hm0 hmmid hmL) (forall_fin_of_ends h0 hL hw0 hwmid hwL)
      (fun a b hab => longEdge_eq_max hn f hf a b hab)
      (fun a b hab => longEdge_eq_zero f hf a b hab)⟩

/-- A chain of at least six minus-two indices with interior weight `c` and constant interior
multiplicity, both of whose end weights are `2 * c`, is case (28). -/
private lemma chain_case_28 (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (i0 iL : Fin T.componentCount) (h0 : i0.val = 0) (hL : iL.val = T.componentCount - 1)
    (c μ : ℤ) (hc : 0 < c)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (hmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.multiplicity (v a) = μ)
    (hw0 : T.weight (v i0) = 2 * c) (hwL : T.weight (v iL) = 2 * c)
    (hμ0 : μ = 2 * T.multiplicity (v i0)) (hμL : μ = 2 * T.multiplicity (v iL)) :
    IsGenusOneConfiguration T := by
  refine isGenusOneConfiguration_of_chain T hn hminus v hvinj hchar .downUp
    (Or.inr (Or.inr rfl)) (T.multiplicity (v i0)) c (T.multiplicity_pos _) hc i0 iL h0 hL ?_
    (fun a hlo hhi => ?_) ?_ ?_ (fun a hlo hhi => ?_) ?_
  · simp only [GenusOne.longMultiplicity, ite_eq_left (Or.inl h0)]
    ring
  · simp only [GenusOne.longMultiplicity, ite_eq_right (show ¬(a.val = 0 ∨
      a.val = T.componentCount - 1) by omega)]
    linarith [hmid a hlo hhi]
  · simp only [GenusOne.longMultiplicity, ite_eq_left (Or.inr (show iL.val =
      T.componentCount - 1 from hL))]
    linarith
  · simp only [GenusOne.longWeight, ite_eq_left (Or.inl h0)]
    linarith
  · simp only [GenusOne.longWeight, ite_eq_right (show ¬(a.val = 0 ∨
      a.val = T.componentCount - 1) by omega)]
    linarith [hcint a hlo hhi]
  · simp only [GenusOne.longWeight, ite_eq_left (Or.inr (show iL.val =
      T.componentCount - 1 from hL))]
    linarith

/-- A chain of at least six minus-two indices with interior weight `c` and constant interior
multiplicity, whose first end weight is half of `c` and whose last is `2 * c`, is case (26). -/
private lemma chain_case_26 (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (i0 iL : Fin T.componentCount) (h0 : i0.val = 0) (hL : iL.val = T.componentCount - 1)
    (c μ : ℤ)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (hmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.multiplicity (v a) = μ)
    (hw0 : 2 * T.weight (v i0) = c) (hwL : T.weight (v iL) = 2 * c)
    (hμ0 : T.multiplicity (v i0) = μ) (hμL : μ = 2 * T.multiplicity (v iL)) :
    IsGenusOneConfiguration T := by
  refine isGenusOneConfiguration_of_chain T hn hminus v hvinj hchar .upUp (Or.inl rfl)
    (T.multiplicity (v iL)) (T.weight (v i0)) (T.multiplicity_pos _) (T.weight_pos _)
    i0 iL h0 hL ?_ (fun a hlo hhi => ?_) ?_ ?_ (fun a hlo hhi => ?_) ?_
  · simp only [GenusOne.longMultiplicity, ite_eq_right (show ¬(i0.val =
      T.componentCount - 1) by omega)]
    linarith
  · simp only [GenusOne.longMultiplicity, ite_eq_right (show ¬(a.val =
      T.componentCount - 1) by omega)]
    linarith [hmid a hlo hhi]
  · simp only [GenusOne.longMultiplicity, ite_eq_left (show iL.val =
      T.componentCount - 1 from hL)]
    ring
  · simp only [GenusOne.longWeight, ite_eq_left (show i0.val = 0 from h0)]
    ring
  · simp only [GenusOne.longWeight, ite_eq_right (show ¬(a.val = 0) by omega),
      ite_eq_right (show ¬(a.val = T.componentCount - 1) by omega)]
    linarith [hcint a hlo hhi]
  · simp only [GenusOne.longWeight, ite_eq_right (show ¬(iL.val = 0) by omega),
      ite_eq_left (show iL.val = T.componentCount - 1 from hL)]
    linarith

/-- A chain of at least six minus-two indices with interior weight `c` and constant interior
multiplicity, whose first end weight is `2 * c` and whose last is half of `c`, is case (26)
read backwards. -/
private lemma chain_case_26_rev (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (i0 iL : Fin T.componentCount) (h0 : i0.val = 0) (hL : iL.val = T.componentCount - 1)
    (c μ : ℤ)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (hmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.multiplicity (v a) = μ)
    (hw0 : T.weight (v i0) = 2 * c) (hwL : 2 * T.weight (v iL) = c)
    (hμ0 : μ = 2 * T.multiplicity (v i0)) (hμL : T.multiplicity (v iL) = μ) :
    IsGenusOneConfiguration T := by
  obtain ⟨rev, hrev, hrevinj, hrevchar⟩ := path_reverse T v hvinj hchar
  have hr : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      1 ≤ (rev a).val ∧ (rev a).val + 1 < T.componentCount := fun a _ _ => by
    have := a.isLt
    rw [hrev a]
    omega
  have hr0 : rev i0 = iL := Fin.ext (by rw [hrev i0]; omega)
  have hrL : rev iL = i0 := Fin.ext (by rw [hrev iL]; omega)
  exact chain_case_26 T hn hminus _ hrevinj hrevchar i0 iL h0 hL c μ
    (fun a hlo hhi => hcint _ (hr a hlo hhi).1 (hr a hlo hhi).2)
    (fun a hlo hhi => hmid _ (hr a hlo hhi).1 (hr a hlo hhi).2)
    (by simp only [hr0]; linarith) (by simp only [hrL]; linarith)
    (by simp only [hr0]; linarith) (by simp only [hrL]; linarith)

/-- A chain of at least six minus-two indices with interior weight `c` and constant interior
multiplicity, both of whose end weights are half of `c`, is case (27). -/
private lemma chain_case_27 (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b))
    (i0 iL : Fin T.componentCount) (h0 : i0.val = 0) (hL : iL.val = T.componentCount - 1)
    (c μ : ℤ)
    (hcint : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.weight (v a) = c)
    (hmid : ∀ a : Fin T.componentCount, 1 ≤ a.val → a.val + 1 < T.componentCount →
      T.multiplicity (v a) = μ)
    (hw0 : 2 * T.weight (v i0) = c) (hwL : 2 * T.weight (v iL) = c)
    (hμ0 : T.multiplicity (v i0) = μ) (hμL : T.multiplicity (v iL) = μ) :
    IsGenusOneConfiguration T := by
  refine isGenusOneConfiguration_of_chain T hn hminus v hvinj hchar .upDown
    (Or.inr (Or.inl rfl)) (T.multiplicity (v i0)) (T.weight (v i0)) (T.multiplicity_pos _)
    (T.weight_pos _) i0 iL h0 hL ?_ (fun a hlo hhi => ?_) ?_ ?_ (fun a hlo hhi => ?_) ?_
  · simp only [GenusOne.longMultiplicity]
    ring
  · simp only [GenusOne.longMultiplicity]
    linarith [hmid a hlo hhi]
  · simp only [GenusOne.longMultiplicity]
    linarith
  · simp only [GenusOne.longWeight, ite_eq_left (Or.inl h0)]
    ring
  · simp only [GenusOne.longWeight, ite_eq_right (show ¬(a.val = 0 ∨
      a.val = T.componentCount - 1) by omega)]
    linarith [hcint a hlo hhi]
  · simp only [GenusOne.longWeight, ite_eq_left (Or.inr (show iL.val =
      T.componentCount - 1 from hL))]
    linarith

/-- A chain ordering of all the components of a numerical type with at least six components,
all of them minus-two indices, is one of the chain families (26), (27) and (28). -/
private lemma isGenusOneConfiguration_of_path (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b)) :
    IsGenusOneConfiguration T := by
  obtain ⟨c, hc, hcint, hcend0, hcendL⟩ := weight_structure_of_path T hn hminus v hvinj hchar
  obtain ⟨i0, hvi0⟩ : ∃ x : Fin T.componentCount, x.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hvi1⟩ : ∃ x : Fin T.componentCount, x.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hvi2⟩ : ∃ x : Fin T.componentCount, x.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨iK, hviK⟩ : ∃ x : Fin T.componentCount, x.val = T.componentCount - 3 :=
    ⟨⟨T.componentCount - 3, by omega⟩, rfl⟩
  obtain ⟨iM, hviM⟩ : ∃ x : Fin T.componentCount, x.val = T.componentCount - 2 :=
    ⟨⟨T.componentCount - 2, by omega⟩, rfl⟩
  obtain ⟨iL, hviL⟩ : ∃ x : Fin T.componentCount, x.val = T.componentCount - 1 :=
    ⟨⟨T.componentCount - 1, by omega⟩, rfl⟩
  have hM0 := T.multiplicity_pos (v i0)
  have hML := T.multiplicity_pos (v iL)
  have hdiffK : T.multiplicity (v iM) - T.multiplicity (v iK)
      = T.multiplicity (v i2) - T.multiplicity (v i1) :=
    chain_diff_const T hn hminus v hvinj hchar c hc hcint i1 i2 hvi1 hvi2
      (T.componentCount - 3) iK iM hviK (by omega) (by omega) (by omega)
  have hR := chain_right_end T hn hminus v hvinj hchar c hc hcint iK iM iL hviK hviM hviL
    (hcendL iL (by omega))
  rcases chain_left_end T hn hminus v hvinj hchar c hc hcint i0 i1 i2 hvi0 hvi1 hvi2
    (hcend0 i0 hvi0) with ⟨-, e0⟩ | ⟨hq0, e1, e2⟩ | ⟨hq0, e1, e2⟩
  · rcases hR with ⟨-, f0⟩ | ⟨-, -, f2⟩ | ⟨-, -, f2⟩ <;> exact (by linarith : False).elim
  all_goals
    have hMconst := chain_multiplicity_const T hn hminus v hvinj hchar c hc hcint i1 i2
      hvi1 hvi2 e2
    have hMM : T.multiplicity (v iM) = T.multiplicity (v i1) := hMconst iM (by omega) (by omega)
    rcases hR with ⟨-, f0⟩ | ⟨hqL, f1, -⟩ | ⟨hqL, f1, -⟩
    · exact (by linarith : False).elim
  · exact chain_case_28 T hn hminus v hvinj hchar i0 iL hvi0 hviL c _ hc hcint hMconst hq0 hqL
      e1 (by linarith)
  · exact chain_case_26_rev T hn hminus v hvinj hchar i0 iL hvi0 hviL c _ hcint hMconst hq0 hqL
      e1 (by linarith)
  · exact chain_case_26 T hn hminus v hvinj hchar i0 iL hvi0 hviL c _ hcint hMconst hq0 hqL
      e1.symm (by linarith)
  · exact chain_case_27 T hn hminus v hvinj hchar i0 iL hvi0 hviL c _ hcint hMconst hq0 hqL
      e1.symm (by linarith)

/-! ### The classification of chains -/

/-- **Stacks Project, Tag 0C8T** for a numerical type each of whose components meets at most two
others. With at least five components it is minimal of genus one exactly when it is the cycle —
case (16) for five components and case (25) for six or more — or one of the chains: cases (17)
to (21) for five components, and cases (26), (27) and (28) for six or more. From six components
on, which of the three chains occurs is decided by the two end weights: both twice the interior
weight gives (28), one half and one twice gives (26), both half gives (27), and an end weight
equal to the interior weight is impossible. -/
@[stacks 0C8T "the classification when every component meets at most two others and there are \
at least five of them: the cycle, cases (16) and (25), and the chains, cases (17)-(21) for five \
components and cases (26), (27) and (28) for six or more"]
public theorem isMinimal_and_genus_eq_one_iff_of_neighborCount_le_two (T : NumericalType)
    (hn : 5 ≤ T.componentCount) (hdeg : ∀ i, neighborCount T i ≤ 2) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T := by
  classical
  refine ⟨fun hT => ?_, isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩
  obtain ⟨hmin, hgenus⟩ := hT
  by_cases hallTwo : ∀ i, 2 ≤ neighborCount T i
  · exact isGenusOneConfiguration_of_two_le_neighborCount T hmin hgenus (by omega) hallTwo
  push Not at hallTwo
  have hminus : ∀ i, IsMinusTwoIndex T i :=
    forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hmin hgenus (by omega)
  obtain ⟨v, hvinj, -, hchar⟩ := exists_path_ordering T (by omega) hdeg hallTwo
  by_cases h5 : T.componentCount = 5
  · exact five_chain_config T h5 hminus v hvinj hchar
  exact isGenusOneConfiguration_of_path T (by omega) hminus v hvinj hchar

end AlgebraicGeometry.NumericalType
