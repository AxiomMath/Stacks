module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Fork
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper subgraphs of type E8

Eight distinct minus-two indices of a numerical type whose indicated
intersections form the Dynkin diagram `E₈` — a seven-vertex chain with a leaf
attached to the fifth vertex — all have the same weight `w` and have the
weighted `E₈` intersection matrix. Their multiplicities satisfy the eight
Cartan inequalities coming from the remaining components.

The common weight comes from the fork classification along the long arm
together with the `D₅` classification along the short arm. The chain entries
then come from the long-chain classification: of its three possible endpoint
scalings only the unscaled one is compatible with a constant weight.

## Main definitions

* `AlgebraicGeometry.NumericalType.e8IntersectionMatrix`: the weighted `E₈`
  intersection matrix.

## Main results

* `AlgebraicGeometry.NumericalType.e8_submatrix_of_minus_two_indices`: an `E₈`
  configuration which is a proper subgraph of a numerical type has constant
  weight and the weighted `E₈` intersection matrix.
* The eight `AlgebraicGeometry.NumericalType.multiplicity_le_of_e8_at_*`
  lemmas: its row-by-row multiplicity inequalities.

## Implementation notes

The eight indices are an injective map from `Fin 8`, so their ordering is part
of the hypotheses and the matrix equality records all sixty-four intersection
numbers at once. The chain is `i 0, …, i 6` and the leaf `i 7` is attached to
`i 4`. The source's assumption `n > 8` is `8 < T.componentCount`.

## References

* [Stacks Project, Tag 0C8L](https://stacks.math.columbia.edu/tag/0C8L)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- The seven vertices of `E₈` forming its `D₇` subdiagram, in fork order. -/
private def e8ForkOrder (j : Fin 7) : Fin 8 :=
  ⟨if j.val = 6 then 7 else j.val, by split_ifs <;> omega⟩

private theorem e8ForkOrder_injective : Function.Injective e8ForkOrder := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [e8ForkOrder] at hv
  split_ifs at hv <;> omega

/-- The five vertices of `E₈` forming the `D₅` subdiagram at the other end. -/
private def e8D5Order (j : Fin 5) : Fin 8 :=
  ⟨if j.val = 4 then 7 else 6 - j.val, by split_ifs <;> omega⟩

private theorem e8D5Order_injective : Function.Injective e8D5Order := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [e8D5Order] at hv
  split_ifs at hv <;> omega

private def e8ForkEmbedding (T : NumericalType)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i) :
    Fin 7 ↪ Fin T.componentCount where
  toFun j := i (e8ForkOrder j)
  inj' := fun _ _ h => e8ForkOrder_injective (hi h)

private def e8D5Embedding (T : NumericalType)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i) :
    Fin 5 ↪ Fin T.componentCount where
  toFun j := i (e8D5Order j)
  inj' := fun _ _ h => e8D5Order_injective (hi h)

/-- A long chain of constant weight `w` has every edge equal to `w` and every
other off-diagonal intersection zero: the two scaled endpoint configurations
are incompatible with a constant weight. -/
private theorem e8_chain_entries (T : NumericalType)
    (f : Fin 7 → Fin T.componentCount)
    (w : ℤ) (hconfig : IsLongChainConfiguration T f)
    (hweight : ∀ j, T.weight (f j) = w) (hw : 0 < w) :
    (∀ j k, k.val = j.val + 1 → T.intersection (f j) (f k) = w) ∧
    (∀ j k, j.val + 1 < k.val → T.intersection (f j) (f k) = 0) := by
  simp only [IsLongChainConfiguration] at hconfig
  rcases hconfig with ⟨w', hsame, hadj, hnon⟩ |
      ⟨w', hpre, hlast, hedge, hedgeLast, hnon⟩ |
      ⟨w', hpre, hlast, hedge, hnon⟩
  · have hw' : w' = w := (hsame (0 : Fin 7)).symm.trans (hweight 0)
    refine ⟨fun j k hjk => ?_, hnon⟩
    rw [hadj j k hjk, hw']
  · have h₀' : w = w' := (hweight 0).symm.trans (hpre (0 : Fin 7) (by decide))
    have h₆' : w = 2 * w' := (hweight 6).symm.trans (hlast (6 : Fin 7) (by decide))
    omega
  · have h₀' : w = 2 * w' := (hweight 0).symm.trans (hpre (0 : Fin 7) (by decide))
    have h₆' : w = w' := (hweight 6).symm.trans (hlast (6 : Fin 7) (by decide))
    omega

/-- The row-balance inequality at a minus-two index of weight `w` whose
intersection number with each selected neighbour is exactly `w`. -/
private theorem e8_balance_row (T : NumericalType)
    (i : Fin 8 → Fin T.componentCount)
    (hi : Function.Injective i) (w : ℤ) (k : Fin 8) (N : Finset (Fin 8))
    (hweight : T.weight (i k) = w)
    (hdiag : T.intersection (i k) (i k) = -2 * w)
    (hentry : ∀ r ∈ N, T.intersection (i k) (i r) = w)
    (hneq : ∀ r ∈ N, r ≠ k) :
    ∑ r ∈ N, T.multiplicity (i r) ≤ 2 * T.multiplicity (i k) := by
  classical
  let f : Fin T.componentCount → ℤ :=
    fun x => T.intersection (i k) x * T.multiplicity x
  let S : Finset (Fin T.componentCount) := N.image i
  have hS : S ⊆ Finset.univ.erase (i k) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    have hri : i r ≠ i k := fun heq => hneq r hr (hi heq)
    simp [hri]
  have hnonneg : ∀ x ∈ Finset.univ.erase (i k), x ∉ S → 0 ≤ f x := fun x hx _ =>
    mul_nonneg (T.intersection_nonneg (i k) x (Finset.ne_of_mem_erase hx).symm)
      (T.multiplicity_pos x).le
  have hsumSub := Finset.sum_le_sum_of_subset_of_nonneg hS hnonneg
  have hsumImage : (∑ x ∈ S, f x) = w * (∑ r ∈ N, T.multiplicity (i r)) := by
    calc
      (∑ x ∈ S, f x) = ∑ r ∈ N, f (i r) :=
        Finset.sum_image (s := N) (g := i) (f := f) (fun a _ b _ hab => hi hab)
      _ = ∑ r ∈ N, w * T.multiplicity (i r) :=
        Finset.sum_congr rfl fun r hr => by simp [f, hentry r hr]
      _ = w * (∑ r ∈ N, T.multiplicity (i r)) := by rw [Finset.mul_sum]
  have hbalance : (∑ x ∈ Finset.univ, f x) = 0 := by
    simpa [f] using T.intersection_mul_multiplicity (i k)
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (i k))] at hbalance
  have hdiagTerm : f (i k) = (-2 * w) * T.multiplicity (i k) := by simp [f, hdiag]
  rw [hdiagTerm] at hbalance
  rw [hsumImage] at hsumSub
  have hw : 0 < w := hweight ▸ T.weight_pos (i k)
  exact (mul_le_mul_iff_left₀ hw).mp (by linarith)

/-- The intersection matrix of the `E₈` tree, with every vertex of weight `w`.
The trivalent vertex is vertex `4`, joined to vertices `3`, `5`, and `7`. -/
public def e8IntersectionMatrix (w : ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  !![-2 * w, w, 0, 0, 0, 0, 0, 0;
      w, -2 * w, w, 0, 0, 0, 0, 0;
      0, w, -2 * w, w, 0, 0, 0, 0;
      0, 0, w, -2 * w, w, 0, 0, 0;
      0, 0, 0, w, -2 * w, w, 0, w;
      0, 0, 0, 0, w, -2 * w, w, 0;
      0, 0, 0, 0, 0, w, -2 * w, 0;
      0, 0, 0, 0, w, 0, 0, -2 * w]

/-- On the short arm of an `E₈` configuration, the `D₅` classification gives
`i 5` and `i 6` equal weight and `i 6` orthogonal to the leaf `i 7`. -/
private theorem e8_d5_arm (T : NumericalType) (hcard : 8 < T.componentCount)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ k, IsMinusTwoIndex T (i k))
    (h45 : T.intersection (i 3) (i 4) ≠ 0)
    (h56 : T.intersection (i 4) (i 5) ≠ 0)
    (h67 : T.intersection (i 5) (i 6) ≠ 0)
    (h58 : T.intersection (i 4) (i 7) ≠ 0) :
    T.weight (i 5) = T.weight (i 6) ∧ T.intersection (i 6) (i 7) = 0 := by
  let vd := e8D5Embedding T i hi
  obtain ⟨wd, hdweights, hdmat⟩ := exists_weight_eq_d5_of_isMinusTwoIndex T (by omega)
    vd (fun j => hminus (e8D5Order j))
    (by simpa [vd, e8D5Embedding, e8D5Order] using
      T.intersection_symm (i 5) (i 6) ▸ h67)
    (by simpa [vd, e8D5Embedding, e8D5Order] using
      T.intersection_symm (i 4) (i 5) ▸ h56)
    (by simpa [vd, e8D5Embedding, e8D5Order] using
      T.intersection_symm (i 3) (i 4) ▸ h45)
    (by simpa [vd, e8D5Embedding, e8D5Order] using h58)
  have h₅ : T.weight (i 5) = wd := by
    simpa [vd, e8D5Embedding, e8D5Order] using congrFun hdweights (1 : Fin 5)
  have h₆ : T.weight (i 6) = wd := by
    simpa [vd, e8D5Embedding, e8D5Order] using congrFun hdweights (0 : Fin 5)
  refine ⟨h₅.trans h₆.symm, ?_⟩
  simpa [vd, e8D5Embedding, e8D5Order] using congrFun (congrFun hdmat (0 : Fin 5)) (4 : Fin 5)

/-- An `E₈` configuration of minus-two indices has constant weight `w`, and the
leaf `i 7` meets the chain `i 0, …, i 6` only at `i 4`, with intersection `w`. -/
private theorem e8_weight_eq_of_minus_two_indices
    (T : NumericalType) (hcard : 8 < T.componentCount)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ k, IsMinusTwoIndex T (i k))
    (h12 : T.intersection (i 0) (i 1) ≠ 0)
    (h23 : T.intersection (i 1) (i 2) ≠ 0)
    (h34 : T.intersection (i 2) (i 3) ≠ 0)
    (h45 : T.intersection (i 3) (i 4) ≠ 0)
    (h56 : T.intersection (i 4) (i 5) ≠ 0)
    (h67 : T.intersection (i 5) (i 6) ≠ 0)
    (h58 : T.intersection (i 4) (i 7) ≠ 0) :
    ∃ w : ℤ, (∀ k, T.weight (i k) = w) ∧
      ∀ j : Fin 7, T.intersection (i 7) (i j.castSucc) = if j = 4 then w else 0 := by
  obtain ⟨h₅₆, h₆₇⟩ := e8_d5_arm T hcard i hi hminus h45 h56 h67 h58
  let vf := e8ForkEmbedding T i hi
  obtain ⟨w, hfw, -, hfb, hfzero⟩ := eq_fork_of_isMinusTwoIndex T 6 (by omega) (by omega)
    vf (fun _ _ h => e8ForkOrder_injective (hi h))
    (fun j => hminus (e8ForkOrder j))
    (by
      intro j
      fin_cases j <;> first
        | simpa [vf, e8ForkEmbedding, e8ForkOrder] using h12
        | simpa [vf, e8ForkEmbedding, e8ForkOrder] using h23
        | simpa [vf, e8ForkEmbedding, e8ForkOrder] using h34
        | simpa [vf, e8ForkEmbedding, e8ForkOrder] using h45
        | simpa [vf, e8ForkEmbedding, e8ForkOrder] using h56)
    (by simpa [vf, e8ForkEmbedding, e8ForkOrder] using h58)
  have hweight : ∀ k : Fin 8, T.weight (i k) = w := by
    intro k
    fin_cases k
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (0 : Fin 7)
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (1 : Fin 7)
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (2 : Fin 7)
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (3 : Fin 7)
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (4 : Fin 7)
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (5 : Fin 7)
    · exact h₅₆.symm.trans (by simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (5 : Fin 7))
    · simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfw (6 : Fin 7)
  refine ⟨w, hweight, fun j => ?_⟩
  split_ifs with h₄
  · subst h₄
    have hb : T.intersection (i 4) (i 7) = w := by
      simpa [vf, e8ForkEmbedding, e8ForkOrder] using hfb
    exact (T.intersection_symm _ _).trans hb
  by_cases h₆ : j = 6
  · subst h₆
    exact (T.intersection_symm _ _).trans h₆₇
  have h₆' : j.val ≠ 6 := fun h => h₆ (Fin.ext h)
  have hz := hfzero (6 : Fin 7) j (Fin.lt_iff_val_lt_val.mpr (by omega))
    (by omega : ¬(6 = j.val + 1 ∧ j.val < 5)) (fun h => h₄ (Fin.ext h.2))
  have hz' : T.intersection (i 7) (i ⟨j.val, by omega⟩) = 0 := by
    simpa [vf, e8ForkEmbedding, e8ForkOrder, h₆'] using hz
  exact hz'

/-- A chain `c` of constant weight `w` whose edges are `w` and whose other
off-diagonal entries vanish has the weighted `A₇` intersection pattern. -/
private theorem chain_intersection_eq_ite (T : NumericalType)
    (c : Fin 7 → Fin T.componentCount) (w : ℤ)
    (hdiag : ∀ j, T.intersection (c j) (c j) = -2 * w)
    (hedge : ∀ j k : Fin 7, k.val = j.val + 1 → T.intersection (c j) (c k) = w)
    (hnon : ∀ j k : Fin 7, j.val + 1 < k.val → T.intersection (c j) (c k) = 0)
    (j k : Fin 7) :
    T.intersection (c j) (c k) =
      if j = k then -2 * w
      else if k.val = j.val + 1 ∨ j.val = k.val + 1 then w else 0 := by
  split_ifs with heq hadj
  · subst heq
    exact hdiag j
  · rcases hadj with hadj | hadj
    · exact hedge j k hadj
    · rw [T.intersection_symm]
      exact hedge k j hadj
  · have hne : j.val ≠ k.val := fun h => heq (Fin.ext h)
    by_cases hlt : j.val < k.val
    · exact hnon j k (by omega)
    · rw [T.intersection_symm]
      exact hnon k j (by omega)

/-- The chain `i 0, …, i 6` of an `E₈` configuration of constant weight `w` has
every edge equal to `w` and every other off-diagonal intersection zero. -/
private theorem e8_chain_edges (T : NumericalType) (hcard : 8 < T.componentCount)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ k, IsMinusTwoIndex T (i k))
    (h12 : T.intersection (i 0) (i 1) ≠ 0)
    (h23 : T.intersection (i 1) (i 2) ≠ 0)
    (h34 : T.intersection (i 2) (i 3) ≠ 0)
    (h45 : T.intersection (i 3) (i 4) ≠ 0)
    (h56 : T.intersection (i 4) (i 5) ≠ 0)
    (h67 : T.intersection (i 5) (i 6) ≠ 0)
    (w : ℤ) (hweight : ∀ k, T.weight (i k) = w) :
    (∀ j k : Fin 7, k.val = j.val + 1 → T.intersection (i j.castSucc) (i k.castSucc) = w) ∧
    (∀ j k : Fin 7, j.val + 1 < k.val → T.intersection (i j.castSucc) (i k.castSucc) = 0) := by
  let c : Fin 7 → Fin T.componentCount := fun j => i ⟨j.val, by omega⟩
  show (∀ j k : Fin 7, k.val = j.val + 1 → T.intersection (c j) (c k) = w) ∧
    (∀ j k : Fin 7, j.val + 1 < k.val → T.intersection (c j) (c k) = 0)
  have hchain := classify_long_chain_of_minus_two_indices T c
    (by decide) (by omega) (by
      intro a b h
      have hh : (⟨a.val, by omega⟩ : Fin 8) = ⟨b.val, by omega⟩ := hi h
      exact Fin.ext (congrArg (fun x : Fin 8 => x.val) hh))
    (fun j => hminus ⟨j.val, by omega⟩)
    (by
      intro j k hjk
      fin_cases j
      · rw [show k = 1 from Fin.ext (by simpa using hjk)]
        simpa [c] using h12
      · rw [show k = 2 from Fin.ext (by simpa using hjk)]
        simpa [c] using h23
      · rw [show k = 3 from Fin.ext (by simpa using hjk)]
        simpa [c] using h34
      · rw [show k = 4 from Fin.ext (by simpa using hjk)]
        simpa [c] using h45
      · rw [show k = 5 from Fin.ext (by simpa using hjk)]
        simpa [c] using h56
      · rw [show k = 6 from Fin.ext (by simpa using hjk)]
        simpa [c] using h67
      · have hk : k.val = 7 := by simpa using hjk
        omega)
  have hw : 0 < w := by
    rw [← hweight 0]
    exact T.weight_pos (i 0)
  rcases hchain with hconfig | hconfig
  · exact e8_chain_entries T c w hconfig (fun j => hweight _) hw
  · have hrev := e8_chain_entries T (fun j => c (Fin.rev j)) w hconfig
      (fun j => hweight _) hw
    refine ⟨fun j k hjk => ?_, fun j k hjk => ?_⟩
    · have hr := hrev.1 (Fin.rev k) (Fin.rev j) (by simp [Fin.rev] at *; omega)
      rwa [T.intersection_symm, Fin.rev_rev, Fin.rev_rev] at hr
    · have hr := hrev.2 (Fin.rev k) (Fin.rev j) (by simp [Fin.rev] at *; omega)
      rwa [T.intersection_symm, Fin.rev_rev, Fin.rev_rev] at hr

/-- **Stacks Project, Tag 0C8L.** A proper `E₈`-shaped configuration of
minus-two indices has constant weight and the weighted `E₈` intersection
matrix. -/
@[stacks 0C8L "weights and intersections"]
public theorem e8_submatrix_of_minus_two_indices
    (T : NumericalType) (hcard : 8 < T.componentCount)
    (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ k, IsMinusTwoIndex T (i k))
    (h12 : T.intersection (i 0) (i 1) ≠ 0)
    (h23 : T.intersection (i 1) (i 2) ≠ 0)
    (h34 : T.intersection (i 2) (i 3) ≠ 0)
    (h45 : T.intersection (i 3) (i 4) ≠ 0)
    (h56 : T.intersection (i 4) (i 5) ≠ 0)
    (h67 : T.intersection (i 5) (i 6) ≠ 0)
    (h58 : T.intersection (i 4) (i 7) ≠ 0) :
    ∃ w : ℤ,
      (∀ k, T.weight (i k) = w) ∧
      (fun k l ↦ T.intersection (i k) (i l)) = e8IntersectionMatrix w := by
  obtain ⟨w, hweight, hleaf⟩ :=
    e8_weight_eq_of_minus_two_indices T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
  have hdiag (j : Fin 8) : T.intersection (i j) (i j) = -2 * w := by
    have hd := (hminus j).2
    rwa [hweight j] at hd
  obtain ⟨hedge, hnon⟩ := e8_chain_edges T hcard i hi hminus h12 h23 h34 h45 h56 h67 w hweight
  refine ⟨w, hweight, funext fun j => funext fun k => ?_⟩
  induction j using Fin.lastCases with
  | last =>
    induction k using Fin.lastCases with
    | last =>
      show T.intersection (i 7) (i 7) = e8IntersectionMatrix w 7 7
      simpa [e8IntersectionMatrix] using hdiag 7
    | cast k =>
      show T.intersection (i 7) (i k.castSucc) = e8IntersectionMatrix w 7 k.castSucc
      rw [hleaf]
      fin_cases k <;> simp [e8IntersectionMatrix]
  | cast j =>
    induction k using Fin.lastCases with
    | last =>
      show T.intersection (i j.castSucc) (i 7) = e8IntersectionMatrix w j.castSucc 7
      rw [T.intersection_symm, hleaf]
      fin_cases j <;> simp [e8IntersectionMatrix]
    | cast k =>
      refine (chain_intersection_eq_ite T (fun j => i j.castSucc) w
        (fun j => hdiag _) hedge hnon j k).trans ?_
      fin_cases j <;> fin_cases k <;> simp [e8IntersectionMatrix]

private theorem e8_matrix_entry (T : NumericalType)
    (i : Fin 8 → Fin T.componentCount) (w : ℤ)
    (hmat : (fun k l ↦ T.intersection (i k) (i l)) = e8IntersectionMatrix w)
    (j k : Fin 8) :
    T.intersection (i j) (i k) = e8IntersectionMatrix w j k :=
  congrFun (congrFun hmat j) k

section

variable (T : NumericalType) (hcard : 8 < T.componentCount)
  (i : Fin 8 → Fin T.componentCount) (hi : Function.Injective i)
  (hminus : ∀ k, IsMinusTwoIndex T (i k))
  (h12 : T.intersection (i 0) (i 1) ≠ 0)
  (h23 : T.intersection (i 1) (i 2) ≠ 0)
  (h34 : T.intersection (i 2) (i 3) ≠ 0)
  (h45 : T.intersection (i 3) (i 4) ≠ 0)
  (h56 : T.intersection (i 4) (i 5) ≠ 0)
  (h67 : T.intersection (i 5) (i 6) ≠ 0)
  (h58 : T.intersection (i 4) (i 7) ≠ 0)

include hcard hi hminus h12 h23 h34 h45 h56 h67 h58

/-- The row-balance inequality of an `E₈` configuration at index `k`, for any set `N` of indices
whose weighted `E₈` entries with `k` all equal the weight. -/
private theorem e8_sum_multiplicity_le (k : Fin 8) (N : Finset (Fin 8))
    (hN : ∀ w : ℤ, ∀ r ∈ N, e8IntersectionMatrix w k r = w) :
    ∑ r ∈ N, T.multiplicity (i r) ≤ 2 * T.multiplicity (i k) := by
  obtain ⟨w, hw, hmat⟩ := e8_submatrix_of_minus_two_indices T hcard i hi hminus
    h12 h23 h34 h45 h56 h67 h58
  have hdiag : e8IntersectionMatrix w k k = -2 * w := by
    fin_cases k <;> simp [e8IntersectionMatrix]
  refine e8_balance_row T i hi w k N (hw k) ((e8_matrix_entry T i w hmat k k).trans hdiag)
    (fun r hr => (e8_matrix_entry T i w hmat k r).trans (hN w r hr)) fun r hr hrk => ?_
  have hwpos : 0 < w := hw k ▸ T.weight_pos (i k)
  have := hN w r hr
  rw [hrk, hdiag] at this
  omega

/-- **Stacks Project, Tag 0C8L.** The first multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "first multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_zero :
    T.multiplicity (i 1) ≤ 2 * T.multiplicity (i 0) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    0 {1} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The second multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "second multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_one :
    T.multiplicity (i 0) + T.multiplicity (i 2) ≤
      2 * T.multiplicity (i 1) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    1 {0, 2} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The third multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "third multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_two :
    T.multiplicity (i 1) + T.multiplicity (i 3) ≤
      2 * T.multiplicity (i 2) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    2 {1, 3} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The fourth multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "fourth multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_three :
    T.multiplicity (i 2) + T.multiplicity (i 4) ≤
      2 * T.multiplicity (i 3) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    3 {2, 4} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The fifth multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "fifth multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_four :
    T.multiplicity (i 3) + T.multiplicity (i 5) + T.multiplicity (i 7) ≤
      2 * T.multiplicity (i 4) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    4 {3, 5, 7} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The sixth multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "sixth multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_five :
    T.multiplicity (i 4) + T.multiplicity (i 6) ≤
      2 * T.multiplicity (i 5) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    5 {4, 6} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The seventh multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "seventh multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_six :
    T.multiplicity (i 5) ≤ 2 * T.multiplicity (i 6) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    6 {5} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

/-- **Stacks Project, Tag 0C8L.** The eighth multiplicity inequality of a
proper `E₈` subgraph. -/
@[stacks 0C8L "eighth multiplicity inequality"]
public theorem multiplicity_le_of_e8_at_seven :
    T.multiplicity (i 4) ≤ 2 * T.multiplicity (i 7) := by
  simpa using e8_sum_multiplicity_le T hcard i hi hminus h12 h23 h34 h45 h56 h67 h58
    7 {4} (by intro w r hr; fin_cases r <;> simp_all [e8IntersectionMatrix])

end

end AlgebraicGeometry.NumericalType
