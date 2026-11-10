module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.ChainEndpoint
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.QuadraticForm
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.D5
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper subgraphs of type D

A *fork* on the components `i 0, …, i t` of a numerical type is a chain
`i 0, …, i (t - 1)` together with a leaf `i t` attached to the penultimate
vertex `i (t - 2)`. This file shows that a fork on more than five minus-two
indices spanning a proper subset of the components has constant weight `w`, that
each of its edges has intersection number exactly `w`, and that all its other
off-diagonal intersection numbers vanish. Equivalently, the restricted
intersection matrix is `w` times the Cartan matrix of the Dynkin diagram `Dₜ₊₁`.

The proof is an induction on `t` that starts from the five-vertex case, which is
the `D₅` classification. The inductive step strips the first vertex, applies the
induction hypothesis to the remaining fork, and then uses the chain endpoint
analysis along each of the fork's two arms to pin down the first vertex. Two of
the three endpoint scalings are ruled out by exhibiting a strictly positive
vector in the zero locus of the intersection form supported on a proper subset
of the components, which cannot exist.

## Main definitions

* `AlgebraicGeometry.NumericalType.ForkShape`: the conjunction of the weight,
  edge, and vanishing conditions on a fork.

## Main results

* `AlgebraicGeometry.NumericalType.eq_fork_of_isMinusTwoIndex`: a long fork of
  minus-two indices has a fork shape.
* `AlgebraicGeometry.NumericalType.exists_forkShape_of_isMinusTwoIndex`: the
  same statement including the five-vertex case, which is `D₅`.
* `AlgebraicGeometry.NumericalType.fork_quadratic_value`: the value of the
  intersection form of a fork on the affine coefficient vector.

## Implementation notes

The source's indices `i₁, …, i_{t+1}` are an injective map from `Fin (t + 1)`,
so positions are zero-based: the chain is `0, …, t - 1` and the leaf is `t`. The
final vanishing condition is stated on the strict lower triangle, as in the
source's phrase "other pairs"; symmetry of the intersection matrix supplies the
upper triangle.

The positive vector used in the two contradiction branches carries coefficient
`2` on the chain's interior and `1` at the two leaves, which is the coefficient
vector of the affine Dynkin diagram the forbidden scaling would produce.

## References

* [Stacks Project, Tag 0C8D](https://stacks.math.columbia.edu/tag/0C8D)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- The numerical shape of a fork of weight `w`: all weights are `w`, the chain
edges and the branch edge have intersection number `w`, and all other
off-diagonal intersection numbers vanish. -/
public def ForkShape (T : NumericalType) (t : ℕ)
    (i : Fin (t + 1) → Fin T.componentCount) (w : ℤ) : Prop :=
  (∀ j, T.weight (i j) = w) ∧
  (∀ j : Fin (t - 1),
    T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) = w) ∧
  T.intersection (i ⟨t - 2, by omega⟩) (i ⟨t, by omega⟩) = w ∧
  (∀ j k : Fin (t + 1), k < j →
    ¬ (j.val = k.val + 1 ∧ k.val < t - 1) →
    ¬ (j.val = t ∧ k.val = t - 2) →
    T.intersection (i j) (i k) = 0)

private lemma succ_sub_two {u : ℕ} (hu : 2 ≤ u) :
    (Fin.succ ⟨u - 2, by omega⟩ : Fin (u + 1 + 1)) = ⟨u + 1 - 2, by omega⟩ :=
  Fin.ext <| by
    simp
    omega

/-- Removing the first vertex of a fork of shape `w` leaves a fork of shape `w`. -/
public lemma ForkShape.tail {T : NumericalType} {u : ℕ} (hu : 2 ≤ u)
    {i : Fin (u + 1 + 1) → Fin T.componentCount} {w : ℤ} (h : ForkShape T (u + 1) i w) :
    ForkShape T u (fun j => i j.succ) w := by
  refine ⟨fun j => h.1 j.succ, fun j => by simpa using h.2.1 ⟨j.val + 1, by omega⟩, ?_, ?_⟩
  · change T.intersection (i (Fin.succ ⟨u - 2, by omega⟩)) (i ⟨u + 1, by omega⟩) = w
    rw [succ_sub_two hu]
    exact h.2.2.1
  · intro j k hkj hnc hnb
    refine h.2.2.2 j.succ k.succ (by simpa using hkj) (fun he => hnc ?_) (fun he => hnb ?_) <;>
      obtain ⟨he1, he2⟩ := he <;> constructor <;> simp at * <;> omega

/-- The quadratic form of the intersection matrix on the vertices `i 0, …, i (u + 1)`,
evaluated on the vector with coefficient `c0` at `i 0`, `2` on the next `u - 1` vertices and
`1` on the last two, in terms of the first diagonal entry, the first edge, and the value of
the form on the tail. -/
public lemma fork_quadratic_head (T : NumericalType) {u : ℕ} (hu : 3 ≤ u)
    (i : Fin (u + 2) → Fin T.componentCount) (w c0 d edge : ℤ)
    (htail : (∑ r : Fin (u + 1), ∑ s : Fin (u + 1),
      (if r.val < u - 1 then 2 else 1) * T.intersection (i r.succ) (i s.succ) *
        (if s.val < u - 1 then 2 else 1)) = -4 * w)
    (hdiag : T.intersection (i 0) (i 0) = d)
    (hedge : T.intersection (i 0) (i 1) = edge)
    (hrow : ∀ j : Fin (u + 1), 0 < j.val → T.intersection (i 0) (i j.succ) = 0) :
    (∑ r : Fin (u + 2), ∑ s : Fin (u + 2),
      (if r.val = 0 then c0 else if r.val < u then 2 else 1) *
        T.intersection (i r) (i s) *
        (if s.val = 0 then c0 else if s.val < u then 2 else 1)) =
      c0 * c0 * d + 2 * (c0 * edge * 2) + -4 * w := by
  classical
  let c : Fin (u + 2) → ℤ := fun j =>
    if j.val = 0 then c0 else if j.val < u then 2 else 1
  let ct : Fin (u + 1) → ℤ := fun j => if j.val < u - 1 then 2 else 1
  have hcShift (j : Fin (u + 1)) : c j.succ = ct j := by
    by_cases hj : j.val < u - 1 <;> simp [c, ct, hj] <;> omega
  let q : Fin (u + 2) → Fin (u + 2) → ℤ := fun r s =>
    c r * T.intersection (i r) (i s) * c s
  have hsplit : (∑ r : Fin (u + 2), ∑ s : Fin (u + 2), q r s) =
      q 0 0 + (∑ s : Fin (u + 1), q 0 s.succ) +
        (∑ r : Fin (u + 1), q r.succ 0) +
          ∑ r : Fin (u + 1), ∑ s : Fin (u + 1), q r.succ s.succ := by
    simp_rw [Fin.sum_univ_succ, Finset.sum_add_distrib]
    ring
  have hcross : (∑ s : Fin (u + 1), q 0 s.succ) = c0 * edge * 2 := by
    let z : Fin (u + 1) := ⟨0, by omega⟩
    have hz : ∀ s ∈ (Finset.univ : Finset (Fin (u + 1))),
        s ∉ ({z} : Finset (Fin (u + 1))) → q 0 s.succ = 0 := by
      intro s _ hs
      have hs0 : s.val ≠ 0 := by
        intro heq
        exact hs (Finset.mem_singleton.mpr (Fin.ext heq))
      simp [q, hrow s (by omega)]
    rw [← Finset.sum_subset (Finset.subset_univ ({z} : Finset _)) hz,
      Finset.sum_singleton]
    have hedge0 : T.intersection (i 0) (i z.succ) = edge := by
      simpa [z] using hedge
    change c 0 * T.intersection (i 0) (i z.succ) * c z.succ = c0 * edge * 2
    rw [hedge0]
    simp [c, z, show 1 < u by omega]
  have hcrossSymm : (∑ r : Fin (u + 1), q r.succ 0) = c0 * edge * 2 :=
    (Finset.sum_congr rfl fun r _ => by
      simp [q, T.intersection_symm]
      ring).trans hcross
  have htailSum : (∑ r : Fin (u + 1), ∑ s : Fin (u + 1), q r.succ s.succ) =
      -4 * w := by
    simpa only [q, hcShift] using htail
  have hq00 : q 0 0 = c0 * c0 * d := by
    simp [q, c, hdiag]
    ring
  have hfull : (∑ r : Fin (u + 2), ∑ s : Fin (u + 2), q r s) =
      c0 * c0 * d + 2 * (c0 * edge * 2) + -4 * w := by
    rw [hsplit, hq00, hcross, hcrossSymm, htailSum]
    ring
  simpa [q, c] using hfull

/-- The quadratic form of the intersection matrix on a fork of shape `w`,
evaluated on the vector with coefficient `2` on the interior of the chain and
`1` at the two leaves, is `-4 * w`. In particular it is negative, which is why
no fork can be completed to an affine diagram. -/
public theorem fork_quadratic_value (T : NumericalType) {t : ℕ} (ht : 3 ≤ t)
    (i : Fin (t + 1) → Fin T.componentCount) (w : ℤ)
    (hminus : ∀ j, IsMinusTwoIndex T (i j)) (hshape : ForkShape T t i w) :
    (∑ r : Fin (t + 1), ∑ s : Fin (t + 1),
      (if r.val < t - 1 then 2 else 1) *
        T.intersection (i r) (i s) *
        (if s.val < t - 1 then 2 else 1)) = -4 * w := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
      by_cases htbase : t = 3
      · subst t
        have hdiag (j : Fin 4) : T.intersection (i j) (i j) = -2 * w := by
          simpa [hshape.1 j] using (hminus j).2
        have h01 : T.intersection (i 0) (i 1) = w := by
          simpa using hshape.2.1 (0 : Fin 2)
        have h12 : T.intersection (i 1) (i 2) = w := by
          simpa using hshape.2.1 (1 : Fin 2)
        have h13 : T.intersection (i 1) (i 3) = w := by
          simpa using hshape.2.2.1
        have h02 : T.intersection (i 0) (i 2) = 0 := by
          simpa [T.intersection_symm] using
            hshape.2.2.2 (2 : Fin 4) 0 (by decide) (by decide) (by decide)
        have h03 : T.intersection (i 0) (i 3) = 0 := by
          simpa [T.intersection_symm] using
            hshape.2.2.2 (3 : Fin 4) 0 (by decide) (by decide) (by decide)
        have h23 : T.intersection (i 2) (i 3) = 0 := by
          simpa [T.intersection_symm] using
            hshape.2.2.2 (3 : Fin 4) 2 (by decide) (by decide) (by decide)
        have h10 : T.intersection (i 1) (i 0) = w := by
          simpa [T.intersection_symm] using h01
        have h20 : T.intersection (i 2) (i 0) = 0 := by
          simpa [T.intersection_symm] using h02
        have h21 : T.intersection (i 2) (i 1) = w := by
          simpa [T.intersection_symm] using h12
        simp_rw [Fin.sum_univ_succ]
        simp [hdiag, h01, h12, h13, h02, h03, h23, h10, h20, h21, T.intersection_symm]
        ring
      · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨t - 1, by omega⟩
        have hu : 3 ≤ u := by omega
        have hrow (j : Fin (u + 1)) (hj : 0 < j.val) :
            T.intersection (i 0) (i j.succ) = 0 := by
          rw [T.intersection_symm]
          refine hshape.2.2.2 j.succ 0 (Fin.succ_pos j) ?_ ?_ <;>
            simp only [Fin.val_succ, Fin.val_zero] <;> omega
        have h := fork_quadratic_head T hu i w 2 (-2 * w) w
          (ih u (by omega) hu (fun j => i j.succ) (fun j => hminus j.succ)
            (hshape.tail (by omega)))
          (by simpa [hshape.1 0] using (hminus 0).2)
          (by simpa using hshape.2.1 ⟨0, by omega⟩) hrow
        refine Eq.trans (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_)
          (h.trans (by ring))
        split_ifs <;> first | rfl | omega

/-- If the first vertex of a fork carries the prescribed diagonal entry, first
edge, and vanishing row, and the three contributions balance to zero, then the
whole quadratic form vanishes on the weighted vector. -/
private lemma fork_endpoint_quadratic_zero (T : NumericalType) {u : ℕ}
    (hu : 3 ≤ u) (e : Fin (u + 2) ↪ Fin T.componentCount) (w c0 d edge : ℤ)
    (hminus : ∀ j, IsMinusTwoIndex T (e j))
    (htail : ForkShape T u (fun j : Fin (u + 1) => e j.succ) w)
    (hdiag : T.intersection (e 0) (e 0) = d)
    (hedge : T.intersection (e 0) (e 1) = edge)
    (hrow : ∀ j : Fin (u + 1), 0 < j.val →
      T.intersection (e 0) (e j.succ) = 0)
    (hbalance : c0 * c0 * d + 2 * (c0 * edge * 2) + (-4 * w) = 0) :
    (∑ r : Fin (u + 2), ∑ s : Fin (u + 2),
      (if r.val = 0 then c0 else if r.val < u then 2 else 1) *
        T.intersection (e r) (e s) *
        (if s.val = 0 then c0 else if s.val < u then 2 else 1)) = 0 :=
  (fork_quadratic_head T hu e w c0 d edge
    (fork_quadratic_value T hu (fun j => e j.succ) w (fun j => hminus j.succ) htail)
    hdiag hedge hrow).trans hbalance

/-- The base case of the fork induction: a fork on five minus-two vertices is
the `D₅` configuration. -/
private lemma fork_base (T : NumericalType) (hn : 4 + 1 < T.componentCount)
    (i : Fin (4 + 1) → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (4 - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0)
    (hbranch : T.intersection (i ⟨4 - 2, by omega⟩) (i ⟨4, by omega⟩) ≠ 0) :
    ∃ w : ℤ, ForkShape T 4 i w := by
  classical
  let v : Fin 5 ↪ Fin T.componentCount := ⟨i, hi⟩
  obtain ⟨w, hw, hmat⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T (by omega) v hminus
    (hchain ⟨0, by omega⟩) (hchain ⟨1, by omega⟩)
    (hchain ⟨2, by omega⟩) hbranch
  refine ⟨w, fun j => ?_, fun j => ?_, ?_, ?_⟩
  · have hj := congrFun hw j
    fin_cases j <;> simpa [v] using hj
  · have hentry :=
      congrFun (congrFun hmat ⟨j.val, by omega⟩) ⟨j.val + 1, by omega⟩
    fin_cases j <;> simpa [v] using hentry
  · simpa [v] using congrFun (congrFun hmat (⟨2, by omega⟩ : Fin 5)) (⟨4, by omega⟩ : Fin 5)
  · intro j k hkj hnotchain hnotbranch
    have hentry := congrFun (congrFun hmat j) k
    fin_cases j <;> fin_cases k <;>
      first
        | simpa [v, Matrix.cons_val_zero] using hentry
        | simp_all

/-- The scaled endpoint cases of the fork induction are impossible: a fork
whose first vertex has weight half or twice the common weight `w` of the rest
yields a strictly positive vector in the zero locus of the intersection form
supported on a proper subset of the components. -/
private lemma fork_endpoint_scaled_absurd (T : NumericalType) {u : ℕ} (hu : 3 ≤ u)
    (E : Fin (u + 2) ↪ Fin T.componentCount) (hsmall : u + 2 < T.componentCount)
    (w c0 edge : ℤ) (hc0 : 0 < c0)
    (hminus : ∀ j, IsMinusTwoIndex T (E j))
    (htail : ForkShape T u (fun j : Fin (u + 1) => E j.succ) w)
    (hedge : T.intersection (E 0) (E 1) = edge)
    (hrow : ∀ j : Fin (u + 1), 0 < j.val →
      T.intersection (E 0) (E j.succ) = 0)
    (hbal : c0 * c0 * (-2 * T.weight (E 0)) + 2 * (c0 * edge * 2) +
      (-4 * w) = 0) :
    False := by
  have hquad := fork_endpoint_quadratic_zero T hu E w c0
    (-2 * T.weight (E 0)) edge hminus htail (hminus 0).2 hedge hrow hbal
  have hc : ∀ j : Fin (u + 2),
      0 < (if j.val = 0 then c0 else if j.val < u then 2 else 1 : ℤ) := fun j => by
    split_ifs <;> omega
  exact no_positive_supported_kernel T (u + 2) E hsmall (by omega)
    (fun j => if j.val = 0 then c0 else if j.val < u then 2 else 1) hc hquad

/-- Along the chain of a long fork of minus-two vertices whose other weights are `w`, the
first vertex falls under one of the three chain endpoint cases and meets no chain vertex
other than the second. -/
public lemma fork_chain_root_pattern (T : NumericalType) {t : ℕ} (ht : 4 < t)
    (hn : t + 1 < T.componentCount) (i : Fin (t + 1) → Fin T.componentCount)
    (hi : Function.Injective i) (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (t - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0) (w : ℤ)
    (hw : ∀ j : Fin (t + 1), 0 < j.val → T.weight (i j) = w) :
    ((T.weight (i ⟨0, by omega⟩) = w ∧
        T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = w) ∨
      (2 * T.weight (i ⟨0, by omega⟩) = w ∧
        T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = w) ∨
      (T.weight (i ⟨0, by omega⟩) = 2 * w ∧
        T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = 2 * w)) ∧
      ∀ j : Fin (t + 1), 2 ≤ j.val → j.val < t →
        T.intersection (i ⟨0, by omega⟩) (i j) = 0 := by
  let path : Fin t → Fin T.componentCount := fun j => i ⟨j.val, by omega⟩
  have hinj : Function.Injective path := by
    intro a b hab
    have hidx : (⟨a.val, by omega⟩ : Fin (t + 1)) = ⟨b.val, by omega⟩ := by
      apply hi
      simpa [path] using hab
    apply Fin.ext
    simpa using congrArg Fin.val hidx
  have hpat := chain_endpoint_pattern T path (by omega) (by omega) hinj
    (fun j => hminus ⟨j.val, by omega⟩)
    (fun j k hjk => by simpa [path, hjk] using hchain ⟨j.val, by omega⟩) w
    (fun j hj _ => hw ⟨j.val, by omega⟩ hj)
  exact ⟨hpat.1, fun j hj hjt => by simpa [path] using hpat.2 ⟨j.val, hjt⟩ hj⟩

/-- The first vertex of a long fork of minus-two vertices whose other weights are `w` does
not meet the leaf of the fork. -/
public lemma fork_root_leaf_eq_zero (T : NumericalType) {t : ℕ} (ht : 4 < t)
    (hn : t + 1 < T.componentCount) (i : Fin (t + 1) → Fin T.componentCount)
    (hi : Function.Injective i) (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (t - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0)
    (hbranch : T.intersection (i ⟨t - 2, by omega⟩) (i ⟨t, by omega⟩) ≠ 0) (w : ℤ)
    (hw : ∀ j : Fin (t + 1), 0 < j.val → T.weight (i j) = w) :
    T.intersection (i ⟨0, by omega⟩) (i ⟨t, by omega⟩) = 0 := by
  let branchPath : Fin t → Fin T.componentCount := fun j =>
    if j.val < t - 1 then i ⟨j.val, by omega⟩ else i ⟨t, by omega⟩
  have hinj : Function.Injective branchPath := by
    intro a b hab
    by_cases ha : a.val < t - 1 <;> by_cases hb : b.val < t - 1
    · apply Fin.ext
      have hidx := hi (by simpa [branchPath, ha, hb] using hab)
      simpa using congrArg Fin.val hidx
    all_goals first
      | (apply Fin.ext; omega)
      | (have hidx := hi (by simpa [branchPath, ha, hb] using hab)
         have hv := congrArg Fin.val hidx
         simp at hv
         omega)
  have hadj : ∀ j k, k.val = j.val + 1 →
      T.intersection (branchPath j) (branchPath k) ≠ 0 := by
    intro j k hjk
    by_cases hj : j.val < t - 2
    · have hk : k.val < t - 1 := by omega
      have hjlt : j.val < t - 1 := by omega
      have hnxt : j.val + 1 < t - 1 := by omega
      simpa [branchPath, hjlt, hnxt, hk, hjk] using hchain ⟨j.val, by omega⟩
    · have hje : j.val = t - 2 := by omega
      have hke : k.val = t - 1 := by omega
      have hjlt : j.val < t - 1 := by omega
      have hte : t - 2 < t - 1 := by omega
      have hknot : ¬ k.val < t - 1 := by omega
      simpa [branchPath, hjlt, hte, hknot, hje, hke] using hbranch
  have hpat := chain_endpoint_pattern T branchPath (by omega) (by omega) hinj
    (fun j => by
      simp only [branchPath]
      split_ifs <;> exact hminus _) hadj w
    (fun j hj hjt => by
      simpa [branchPath, show j.val < t - 1 by omega] using hw ⟨j.val, by omega⟩ hj)
  simpa [branchPath, show 0 < t - 1 by omega, show ¬ (t - 1) < t - 1 by omega] using
    hpat.2 ⟨t - 1, by omega⟩ (show 2 ≤ t - 1 by omega)

/-- A fork whose tail has shape `w`, whose first vertex has weight `w`, and whose first
vertex meets the second in `w` and no other vertex, has shape `w`. -/
public lemma ForkShape.of_tail {T : NumericalType} {u : ℕ} (hu : 2 ≤ u)
    {i : Fin (u + 1 + 1) → Fin T.componentCount} {w : ℤ}
    (htail : ForkShape T u (fun j => i j.succ) w) (hwt : T.weight (i 0) = w)
    (hedge : T.intersection (i 0) (i 1) = w)
    (hrow : ∀ j : Fin (u + 1 + 1), 2 ≤ j.val → T.intersection (i 0) (i j) = 0) :
    ForkShape T (u + 1) i w := by
  refine ⟨fun j => Fin.cases hwt htail.1 j, fun j => ?_, ?_, fun j k hkj hnc hnb => ?_⟩
  · by_cases hj : j.val = 0
    · simpa [hj] using hedge
    · have e : j.val - 1 + 1 = j.val := by omega
      simpa [e] using htail.2.1 ⟨j.val - 1, by omega⟩
  · rw [← succ_sub_two hu]
    exact htail.2.2.1
  · by_cases hk : k.val = 0
    · have hne : j.val ≠ 1 := fun hj => hnc ⟨by omega, by omega⟩
      have hj : 2 ≤ j.val := by omega
      rw [show k = 0 from Fin.ext (by simpa using hk), T.intersection_symm]
      exact hrow j hj
    · obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero (show k ≠ 0 from fun h => hk (by simp [h]))
      obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero ((Fin.succ_pos b).trans hkj).ne'
      simp only [Fin.val_succ] at hnc hnb
      exact htail.2.2.2 a b (Fin.succ_lt_succ_iff.mp hkj) (by omega) (by omega)

/-- A long fork of minus-two vertices inside a proper subset of the components whose tail
has shape `w` has shape `w` itself: the two scaled endpoint cases are impossible. -/
public lemma forkShape_of_tail (T : NumericalType) {u : ℕ} (hu : 4 ≤ u)
    (hn : u + 1 + 1 < T.componentCount) (i : Fin (u + 1 + 1) → Fin T.componentCount)
    (hi : Function.Injective i) (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (u + 1 - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0)
    (hbranch : T.intersection (i ⟨u + 1 - 2, by omega⟩) (i ⟨u + 1, by omega⟩) ≠ 0)
    {w : ℤ} (hw : ForkShape T u (fun j => i j.succ) w) : ForkShape T (u + 1) i w := by
  have hwt (j : Fin (u + 1 + 1)) (hj : 0 < j.val) : T.weight (i j) = w := by
    rw [← Fin.succ_pred j (by rintro rfl; simp at hj)]
    exact hw.1 _
  obtain ⟨hcase, hzero⟩ :=
    fork_chain_root_pattern T (t := u + 1) (by omega) hn i hi hminus hchain w hwt
  have hroot (j : Fin (u + 1 + 1)) (hj : 2 ≤ j.val) : T.intersection (i 0) (i j) = 0 := by
    by_cases hjt : j.val = u + 1
    · rw [show j = ⟨u + 1, by omega⟩ from Fin.ext hjt]
      simpa using fork_root_leaf_eq_zero T (t := u + 1) (by omega) hn i hi hminus hchain
        hbranch w hwt
    · simpa using hzero j hj (by omega)
  let E : Fin (u + 2) ↪ Fin T.componentCount := ⟨i, hi⟩
  have hrow (j : Fin (u + 1)) (hj : 0 < j.val) : T.intersection (E 0) (E j.succ) = 0 := by
    simpa [E] using hroot j.succ (by rw [Fin.val_succ]; omega)
  rcases hcase with ⟨hwt0, hedge⟩ | ⟨hwt0, hedge⟩ | ⟨hwt0, hedge⟩
  · exact hw.of_tail (by omega) (by simpa using hwt0) (by simpa using hedge) hroot
  · have hwtE : 2 * T.weight (E 0) = w := by simpa [E] using hwt0
    exact (fork_endpoint_scaled_absurd T (u := u) (by omega) E hn w 2 w (by norm_num)
      hminus hw (by simpa [E] using hedge) hrow (by linear_combination -4 * hwtE)).elim
  · have hwtE : T.weight (E 0) = 2 * w := by simpa [E] using hwt0
    exact (fork_endpoint_scaled_absurd T (u := u) (by omega) E hn w 1 (2 * w) (by norm_num)
      hminus hw (by simpa [E] using hedge) hrow (by linear_combination -2 * hwtE)).elim

/-- A fork on at least five minus-two vertices inside a proper subset of the
components of a numerical type has constant weights, with every edge equal to
that weight and every other off-diagonal intersection equal to zero.

This is `eq_fork_of_isMinusTwoIndex` with the five-vertex case `t = 4`
included; there the fork is the Dynkin diagram `D₅`. -/
public theorem exists_forkShape_of_isMinusTwoIndex
    (T : NumericalType) (t : ℕ) (ht : 3 < t)
    (hn : t + 1 < T.componentCount)
    (i : Fin (t + 1) → Fin T.componentCount)
    (hi : Function.Injective i)
    (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (t - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0)
    (hbranch : T.intersection (i ⟨t - 2, by omega⟩)
      (i ⟨t, Nat.lt_succ_self t⟩) ≠ 0) :
    ∃ w : ℤ, ForkShape T t i w := by
  revert ht hn i hi hminus hchain hbranch
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht hn i hi hminus hchain hbranch
      by_cases htbase : t = 4
      · subst t
        exact fork_base T hn i hi hminus hchain hbranch
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        obtain ⟨w, hw⟩ := ih u (by omega) (by omega) (by omega) (fun j => i j.succ)
          (hi.comp (Fin.succ_injective _)) (fun j => hminus j.succ)
          (fun j => by simpa using hchain ⟨j.val + 1, by omega⟩) (by
            change T.intersection (i (Fin.succ ⟨u - 2, by omega⟩)) (i ⟨u + 1, by omega⟩) ≠ 0
            rw [succ_sub_two (by omega)]
            exact hbranch)
        exact ⟨w, forkShape_of_tail T (by omega) hn i hi hminus hchain hbranch hw⟩

/-- **Stacks Project, Tag 0C8D.** A fork on more than five minus-two vertices
inside a proper subset of the components of a numerical type has constant
weights, with every edge equal to that weight and every other off-diagonal
intersection equal to zero. -/
@[stacks 0C8D]
public theorem eq_fork_of_isMinusTwoIndex
    (T : NumericalType) (t : ℕ) (ht : 4 < t)
    (hn : t + 1 < T.componentCount)
    (i : Fin (t + 1) → Fin T.componentCount)
    (hi : Function.Injective i)
    (hminus : ∀ j, IsMinusTwoIndex T (i j))
    (hchain : ∀ j : Fin (t - 1),
      T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) ≠ 0)
    (hbranch : T.intersection (i ⟨t - 2, by omega⟩) (i ⟨t, by omega⟩) ≠ 0) :
    ∃ w : ℤ,
      (∀ j, T.weight (i j) = w) ∧
      (∀ j : Fin (t - 1),
        T.intersection (i ⟨j, by omega⟩) (i ⟨j + 1, by omega⟩) = w) ∧
      T.intersection (i ⟨t - 2, by omega⟩) (i ⟨t, by omega⟩) = w ∧
      (∀ j k : Fin (t + 1), k < j →
          ¬ (j.val = k.val + 1 ∧ k.val < t - 1) →
          ¬ (j.val = t ∧ k.val = t - 2) →
          T.intersection (i j) (i k) = 0) :=
  exists_forkShape_of_isMinusTwoIndex T t (by omega) hn i hi hminus hchain hbranch

end AlgebraicGeometry.NumericalType
