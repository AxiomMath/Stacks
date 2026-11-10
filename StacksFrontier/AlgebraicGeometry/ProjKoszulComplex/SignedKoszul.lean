module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex of a sequence, in coordinates indexed by subsets

Let `B` be a commutative ring and `f₀, …, f_{m-1}` elements of `B`. The Koszul complex of the
sequence has as its `j`-th cochain group the free module on the `j`-element subsets of
`Fin m`, and its differential sends the basis vector `e_s` to `∑_{k ∉ s} ε(k, s) f_k e_{s ∪ k}`
where the sign `ε(k, s) = (-1) ^ #{l ∈ s | l < k}` counts the elements of `s` that `k` has to
cross. This file develops that complex in coordinates: a cochain in degree `j` is a function on
subsets, the differential is `koszulDiffFun`, and the contraction with the `i`-th coordinate
functional is `koszulHtpyFun`.

The one result the rest of the development needs is that when `f_i = 1` the contraction is a
contracting homotopy: `d ∘ h + h ∘ d` is the identity. Consequently a cochain in the kernel of
the differential is a coboundary, which is `exists_sum_koszulRatioCoeff_eq`.

Everything here is grading-free: a cochain is a function on *all* subsets, and the grading is
re-imposed only at the interface, by `koszulExtend`, which extends a function on the
`j`-element subsets by zero. That is what keeps the signs and the two-term cancellations free
of arithmetic on the degrees.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulSign`: the sign `(-1) ^ #{l ∈ s | l < k}`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulIndex`: the subsets of `Fin m` of a given
  cardinality, the index type of the `j`-th cochain group.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulExtend`: a function on the `j`-element
  subsets, extended by zero to all subsets.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulDiffFun` and
  `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulHtpyFun`: the Koszul differential and the
  contraction with the `i`-th coordinate functional, on functions on subsets.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulRatioCoeff`: the matrix entry of the
  differential from the `s`-th to the `t`-th coordinate.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulSign_mul_self`: the sign squares to one.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulSign_insert_mul_koszulSign_insert`: the
  two ways of inserting `i` and `k` into a subset contribute opposite signs, the identity
  behind both `d ∘ d = 0` and the homotopy, together with the additive form
  `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulSign_pair_add_eq_zero`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.card_koszulIndex`: there are `binom(m, j)` subsets
  of `Fin m` with `j` elements.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.sum_koszulRatioCoeff_mul`: the matrix form of the
  differential agrees with the `erase` form.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulDiffFun_koszulHtpyFun`: **if `f_i = 1` then
  the contraction with the `i`-th coordinate functional is a contracting homotopy.**
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.exists_sum_koszulRatioCoeff_eq`: **if `f_i = 1`,
  a cochain annihilated by the differential is a coboundary.**

## References

* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public section

universe u

namespace Stacks.AlgebraicGeometry.ProjKoszulComplex

variable {m : ℕ} {B : Type u} [CommRing B]

/-! ### The Koszul sign -/

/-- The sign with which `k` is inserted into the subset `s`: `(-1)` to the number of elements of
`s` smaller than `k`. -/
def koszulSign (k : Fin m) (s : Finset (Fin m)) : ℤ :=
  (-1) ^ (s.filter fun l => l < k).card

/-- The Koszul sign squares to one. -/
theorem koszulSign_mul_self (k : Fin m) (s : Finset (Fin m)) :
    koszulSign k s * koszulSign k s = 1 := by
  rw [koszulSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- The Koszul sign squares to one, in any commutative ring. -/
theorem cast_koszulSign_mul_self (k : Fin m) (s : Finset (Fin m)) :
    ((koszulSign k s : ℤ) : B) * ((koszulSign k s : ℤ) : B) = 1 := by
  rw [← Int.cast_mul, koszulSign_mul_self, Int.cast_one]

/-- Adding an element not below `k` to a subset does not change the sign of `k`. -/
theorem koszulSign_insert_of_not_lt {k b : Fin m} (s : Finset (Fin m)) (h : ¬ b < k) :
    koszulSign k (insert b s) = koszulSign k s := by
  rw [koszulSign, koszulSign, Finset.filter_insert, ite_eq_right h]

/-- Adding a new element below `k` to a subset flips the sign of `k`. -/
theorem koszulSign_insert_of_lt {k b : Fin m} {s : Finset (Fin m)} (h : b < k) (hb : b ∉ s) :
    koszulSign k (insert b s) = - koszulSign k s := by
  rw [koszulSign, koszulSign, Finset.filter_insert, ite_eq_left h,
    Finset.card_insert_of_notMem (fun hc => hb (Finset.mem_filter.1 hc).1), pow_succ]
  ring

/-- **Inserting two elements into a subset in the two possible orders contributes opposite
signs.** Exactly one of `i < k` and `k < i` holds, and the corresponding insertion flips its
sign while the other does not. -/
theorem koszulSign_insert_mul_koszulSign_insert {i k : Fin m} (hik : i ≠ k)
    {s : Finset (Fin m)} (hi : i ∉ s) (hk : k ∉ s) :
    koszulSign i (insert k s) * koszulSign k (insert i s) =
      -(koszulSign i s * koszulSign k s) := by
  rcases lt_or_gt_of_ne hik with h | h
  · rw [koszulSign_insert_of_not_lt s (not_lt_of_gt h), koszulSign_insert_of_lt h hi]
    ring
  · rw [koszulSign_insert_of_lt h hk, koszulSign_insert_of_not_lt s (not_lt_of_gt h)]
    ring

/-- **The two orders of inserting `i` and `i'` into a subset contribute opposite signs.** This
is the form in which the cancellation enters `d ∘ d = 0`: the two signs multiply to `-1` and
each squares to `1`, so they sum to zero. -/
theorem koszulSign_pair_add_eq_zero {i i' : Fin m} (hii' : i ≠ i') {s : Finset (Fin m)}
    (hi : i ∉ s) (hi' : i' ∉ s) :
    koszulSign i s * koszulSign i' (insert i s) +
      koszulSign i' s * koszulSign i (insert i' s) = 0 := by
  linear_combination (koszulSign i' s * koszulSign i' (insert i s)) *
      koszulSign_insert_mul_koszulSign_insert hii' hi hi' -
    (koszulSign i' s * koszulSign i (insert i' s)) * koszulSign_mul_self i' (insert i s) -
    (koszulSign i s * koszulSign i' (insert i s)) * koszulSign_mul_self i' s

/-! ### Cochains in a fixed degree -/

/-- The subsets of `Fin m` with `j` elements, `j` an integer: empty unless `0 ≤ j ≤ m`. This is
the index type of the `j`-th cochain group of the Koszul complex. -/
abbrev koszulIndex (m : ℕ) (j : ℤ) := {s : Finset (Fin m) // (s.card : ℤ) = j}

/-- **There are `binom(m, j)` subsets of `Fin m` with `j` elements**, so that is the rank of the
`j`-th cochain group of the Koszul complex on `m` elements. -/
theorem card_koszulIndex (m j : ℕ) :
    Fintype.card (koszulIndex m (j : ℤ)) = m.choose j := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Nat.cast_inj (R := ℤ)),
    Fintype.card_finset_len, Fintype.card_fin]

/-- Removing an element of a `j + 1`-element subset gives a `j`-element subset. -/
def koszulErase {j : ℤ} (t : koszulIndex m (j + 1)) {k : Fin m} (hk : k ∈ t.1) :
    koszulIndex m j :=
  ⟨t.1.erase k, by
    rw [Finset.card_erase_of_mem hk, Nat.cast_sub (Finset.card_pos.2 ⟨k, hk⟩), Nat.cast_one, t.2]
    ring⟩

/-- Adding a new element to a `j`-element subset gives a `j + 1`-element subset. -/
def koszulInsert {j : ℤ} (s : koszulIndex m j) {k : Fin m} (hk : k ∉ s.1) :
    koszulIndex m (j + 1) :=
  ⟨insert k s.1, by rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, s.2]⟩

/-- A cochain in degree `j`, read as a function on all subsets by extending it by zero. -/
def koszulExtend {j : ℤ} (c : koszulIndex m j → B) (s : Finset (Fin m)) : B :=
  if h : (s.card : ℤ) = j then c ⟨s, h⟩ else 0

/-- The zero extension of a degree-`j` cochain agrees with it on `j`-element subsets. -/
theorem koszulExtend_apply {j : ℤ} (c : koszulIndex m j → B) (s : koszulIndex m j) :
    koszulExtend c s.1 = c s :=
  dite_eq_left s.2

/-- The zero extension of a degree-`j` cochain vanishes on subsets without `j` elements. -/
theorem koszulExtend_of_ne {j : ℤ} (c : koszulIndex m j → B) {s : Finset (Fin m)}
    (h : (s.card : ℤ) ≠ j) : koszulExtend c s = 0 :=
  dite_eq_right h

/-- The zero extension of a degree-`j` cochain, at `t \ {k}` for `k ∈ t` and `t` a `j + 1`-element
subset, is the value of the cochain at `koszulErase t hk`. -/
theorem koszulExtend_erase {j : ℤ} (c : koszulIndex m j → B) (t : koszulIndex m (j + 1))
    {k : Fin m} (hk : k ∈ t.1) : koszulExtend c (t.1.erase k) = c (koszulErase t hk) :=
  koszulExtend_apply c (koszulErase t hk)

/-! ### The differential and the contraction -/

/-- **The Koszul differential**, on functions on subsets: the value at `t` is the signed sum of
the values at the subsets obtained by removing one element of `t`, weighted by the corresponding
entry of the sequence. -/
def koszulDiffFun (f : Fin m → B) (c : Finset (Fin m) → B) (t : Finset (Fin m)) : B :=
  ∑ k ∈ t, ((koszulSign k (t.erase k) : ℤ) : B) * f k * c (t.erase k)

/-- **Contraction with the `i`-th coordinate functional**, on functions on subsets: the value at
`s` is the value at `s ∪ {i}` with its sign, or zero if `i` already lies in `s`. -/
def koszulHtpyFun (i : Fin m) (c : Finset (Fin m) → B) (s : Finset (Fin m)) : B :=
  if i ∈ s then 0 else ((koszulSign i s : ℤ) : B) * c (insert i s)

/-- The matrix entry of the Koszul differential from the `s`-th to the `t`-th coordinate: the
signed entry `ε(k, s) f_k` when `t` is `s` with one new element `k`, and zero otherwise. -/
def koszulRatioCoeff (f : Fin m → B) {j : ℤ} (s : koszulIndex m j)
    (t : koszulIndex m (j + 1)) : B :=
  ∑ k : Fin m, if t.1 = insert k s.1 ∧ k ∉ s.1 then ((koszulSign k s.1 : ℤ) : B) * f k else 0

/-- The matrix entry at a pair of indices differing by one element `k` is the signed entry
`ε(k, s) f_k`. The element `k` is determined by the pair, so the sum defining the entry has only
this one nonzero term. -/
theorem koszulRatioCoeff_eq (f : Fin m → B) {j : ℤ} (s : koszulIndex m j)
    (t : koszulIndex m (j + 1)) {k : Fin m} (hk : k ∉ s.1) (ht : t.1 = insert k s.1) :
    koszulRatioCoeff f s t = ((koszulSign k s.1 : ℤ) : B) * f k := by
  classical
  refine Eq.trans (Finset.sum_eq_single_of_mem k (Finset.mem_univ k) ?_) (ite_eq_left ⟨ht, hk⟩)
  intro b _ hb
  refine ite_eq_right fun h => hb ?_
  have hbt : b ∈ insert k s.1 := ht ▸ h.1 ▸ Finset.mem_insert_self b s.1
  exact (Finset.mem_insert.1 hbt).resolve_right h.2

/-- The matrix entry at a pair of indices not differing by a single new element vanishes. -/
theorem koszulRatioCoeff_eq_zero (f : Fin m → B) {j : ℤ} (s : koszulIndex m j)
    (t : koszulIndex m (j + 1)) (h : ∀ k : Fin m, k ∉ s.1 → t.1 ≠ insert k s.1) :
    koszulRatioCoeff f s t = 0 :=
  Finset.sum_eq_zero fun k _ => ite_eq_right fun hc => h k hc.2 hc.1

/-- **The matrix form of the Koszul differential agrees with its `erase` form.** Summing the
matrix entries against a cochain of degree `j` computes the differential of its extension by
zero. -/
theorem sum_koszulRatioCoeff_mul (f : Fin m → B) {j : ℤ} (c : koszulIndex m j → B)
    (t : koszulIndex m (j + 1)) :
    ∑ s : koszulIndex m j, koszulRatioCoeff f s t * c s =
      koszulDiffFun f (koszulExtend c) t := by
  classical
  have h1 : ∀ s : koszulIndex m j, koszulRatioCoeff f s t * c s =
      ∑ k : Fin m, if t.1 = insert k s.1 ∧ k ∉ s.1 then
        ((koszulSign k s.1 : ℤ) : B) * f k * c s else 0 :=
    fun s => by simp only [koszulRatioCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => h1 s, Finset.sum_comm, koszulDiffFun]
  refine (Finset.sum_subset (Finset.subset_univ t.1) ?_).symm.trans ?_
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ => ite_eq_right ?_
    exact fun h => hk (h.1 ▸ Finset.mem_insert_self k s.1)
  · refine Finset.sum_congr rfl fun k hk => ?_
    refine (Finset.sum_eq_single_of_mem (koszulErase t hk) (Finset.mem_univ _) ?_).trans ?_
    · intro s _ hs
      refine ite_eq_right fun h => hs (Subtype.ext ?_)
      change s.1 = t.1.erase k
      rw [h.1, Finset.erase_insert h.2]
    · refine Eq.trans (ite_eq_left ⟨(Finset.insert_erase hk).symm,
        Finset.notMem_erase k t.1⟩) ?_
      exact congrArg (fun b : B => ((koszulSign k (t.1.erase k) : ℤ) : B) * f k * b)
        (koszulExtend_erase c t hk).symm

/-- The differential at `t` only depends on the values of the cochain at the subsets obtained
by removing one element of `t`. -/
theorem koszulDiffFun_congr (f : Fin m → B) {c c' : Finset (Fin m) → B} (t : Finset (Fin m))
    (h : ∀ k ∈ t, c (t.erase k) = c' (t.erase k)) :
    koszulDiffFun f c t = koszulDiffFun f c' t :=
  Finset.sum_congr rfl fun k hk => congrArg _ (h k hk)

/-- **Contraction with the `i`-th coordinate functional is a contracting homotopy when the
`i`-th entry of the sequence is `1`.**

If `i ∈ t` only the term removing `i` survives in `d(h c)(t)`, and the two signs it carries
cancel. If `i ∉ t` the term of `h(d c)(t)` removing `i` again gives `c t`, and each remaining
term cancels against the corresponding term of `d(h c)(t)` by
`koszulSign_insert_mul_koszulSign_insert`. -/
@[ega "III 1.1.8" "special case"]
theorem koszulDiffFun_koszulHtpyFun (f : Fin m → B) {i : Fin m} (hfi : f i = 1)
    (c : Finset (Fin m) → B) (t : Finset (Fin m)) :
    koszulDiffFun f (koszulHtpyFun i c) t + koszulHtpyFun i (koszulDiffFun f c) t = c t := by
  classical
  by_cases hit : i ∈ t
  · rw [koszulHtpyFun, ite_eq_left hit, add_zero, koszulDiffFun,
      Finset.sum_eq_single_of_mem i hit ?_]
    · rw [koszulHtpyFun, ite_eq_right (Finset.notMem_erase i t), Finset.insert_erase hit, hfi,
        mul_one, ← mul_assoc, cast_koszulSign_mul_self, one_mul]
    · intro k hk hki
      rw [koszulHtpyFun, ite_eq_left (Finset.mem_erase.2 ⟨Ne.symm hki, hit⟩), mul_zero]
  · have hiek : ∀ k ∈ t, i ∉ t.erase k := fun k _ h => hit (Finset.mem_erase.1 h).2
    have hik : ∀ k ∈ t, i ≠ k := fun k hk h => hit (h ▸ hk)
    have hA : koszulDiffFun f (koszulHtpyFun i c) t =
        ∑ k ∈ t, ((koszulSign k (t.erase k) : ℤ) : B) * f k *
          (((koszulSign i (t.erase k) : ℤ) : B) * c (insert i (t.erase k))) :=
      Finset.sum_congr rfl fun k hk => by
        rw [koszulHtpyFun, ite_eq_right (hiek k hk)]
    have hB : koszulDiffFun f c (insert i t) = ((koszulSign i t : ℤ) : B) * c t +
        ∑ k ∈ t, ((koszulSign k (insert i (t.erase k)) : ℤ) : B) * f k *
          c (insert i (t.erase k)) := by
      rw [koszulDiffFun, Finset.sum_insert hit, Finset.erase_insert hit, hfi, mul_one]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [Finset.erase_insert_of_ne (hik k hk)]
    have hzero : (∑ k ∈ t, ((koszulSign k (t.erase k) : ℤ) : B) * f k *
          (((koszulSign i (t.erase k) : ℤ) : B) * c (insert i (t.erase k)))) +
        ((koszulSign i t : ℤ) : B) * ∑ k ∈ t,
          ((koszulSign k (insert i (t.erase k)) : ℤ) : B) * f k *
            c (insert i (t.erase k)) = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [congrArg (koszulSign i) (Finset.insert_erase hk).symm]
      have hcast : ((koszulSign i (insert k (t.erase k)) : ℤ) : B) *
          ((koszulSign k (insert i (t.erase k)) : ℤ) : B) =
          -(((koszulSign i (t.erase k) : ℤ) : B) *
            ((koszulSign k (t.erase k) : ℤ) : B)) := by
        rw [← Int.cast_mul, koszulSign_insert_mul_koszulSign_insert (hik k hk) (hiek k hk)
          (Finset.notMem_erase k t), Int.cast_neg, Int.cast_mul]
      linear_combination (f k * c (insert i (t.erase k))) * hcast
    rw [koszulHtpyFun, ite_eq_right hit, hA, hB]
    linear_combination hzero + c t * cast_koszulSign_mul_self (B := B) i t

/-- **A cochain annihilated by the Koszul differential is a coboundary, as soon as one entry of
the sequence is `1`.** The witness is the contraction of the cochain with the corresponding
coordinate functional. -/
theorem exists_sum_koszulRatioCoeff_eq (f : Fin m → B) {i : Fin m} (hfi : f i = 1) (j : ℤ)
    (c : koszulIndex m (j + 1) → B)
    (hc : ∀ u : koszulIndex m (j + 1 + 1),
      ∑ t : koszulIndex m (j + 1), koszulRatioCoeff f t u * c t = 0) :
    ∃ v : koszulIndex m j → B,
      ∀ t : koszulIndex m (j + 1), ∑ s : koszulIndex m j, koszulRatioCoeff f s t * v s = c t := by
  classical
  have hC : ∀ u : Finset (Fin m), koszulDiffFun f (koszulExtend c) u = 0 := by
    intro u
    by_cases hu : (u.card : ℤ) = j + 1 + 1
    · exact (sum_koszulRatioCoeff_mul f c ⟨u, hu⟩).symm.trans (hc ⟨u, hu⟩)
    · refine Finset.sum_eq_zero fun k hk => ?_
      have hne : (((u.erase k).card : ℕ) : ℤ) ≠ j + 1 := by
        rw [Finset.card_erase_of_mem hk, Nat.cast_sub (Finset.card_pos.2 ⟨k, hk⟩), Nat.cast_one]
        omega
      rw [koszulExtend_of_ne c hne, mul_zero]
  refine ⟨fun s => koszulHtpyFun i (koszulExtend c) s.1, fun t => ?_⟩
  rw [sum_koszulRatioCoeff_mul]
  refine Eq.trans (koszulDiffFun_congr f (c' := koszulHtpyFun i (koszulExtend c)) t.1
    fun k hk => ?_) ?_
  · exact koszulExtend_apply (fun s : koszulIndex m j => koszulHtpyFun i (koszulExtend c) s.1)
      (koszulErase t hk)
  · have hH : koszulHtpyFun i (koszulDiffFun f (koszulExtend c)) t.1 = 0 := by
      by_cases hit : i ∈ t.1
      · rw [koszulHtpyFun, ite_eq_left hit]
      · rw [koszulHtpyFun, ite_eq_right hit, hC, mul_zero]
    have key := koszulDiffFun_koszulHtpyFun f hfi (koszulExtend c) t.1
    rw [hH, add_zero] at key
    exact key.trans (koszulExtend_apply c t)

end Stacks.AlgebraicGeometry.ProjKoszulComplex

end
