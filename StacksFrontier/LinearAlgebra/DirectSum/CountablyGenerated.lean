module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Direct summands of direct sums of countably generated modules

Let `M` be a module over a ring `R` which is the internal direct sum of an independent family of
countably generated submodules, and let `P` be a direct summand of `M`, with complement `Q`. This
file proves that `P` is again such a direct sum. This is Kaplansky's theorem that the class of
direct sums of countably generated modules is closed under direct summands.

Write `M = ⨁_{i ∈ I} N_i` with each `N_i` countably generated, and let `pr : M → M` be the
projection onto `P` along `Q`. Call a set `J ⊆ I` *closed* when the submodule `M_J = ⨆_{i ∈ J} N_i`
is stable under `pr`. Choosing countably many generators of each `N_i` and, for each element of
`M`, a countable set of indices supporting it, one obtains a countably-valued map `f : I → Set I`
such that `J` is closed as soon as `f i ⊆ J` for every `i ∈ J`. Hence every subset of `I` is
contained in a closed set with countable overhead, and after well-ordering `I` the sets `V i`
obtained this way form a continuous increasing chain of closed sets exhausting `I` with countable
successive differences. Because `M_{V i}` is `pr`-stable and the partial supremum
`⨆_{j < i} M_{V j}` is both `pr`-stable and a direct summand of `M`, the trace of `P` on that
partial supremum is a direct summand of `M`, hence of the trace of `P` on `M_{V i}`; a complement
`C i` of it there is countably generated, because the trace of `P` on `M_{V i}` is generated over
the trace of `P` on the partial supremum by the *projections* of countably many elements. The
submodules `C i` are then independent with supremum `P`.

## Main results

* `Stacks.DirectSum.KaplanskySummand.solution`: the proof of Stacks 058X, as stated in
  `Submodule.exists_sSupIndep_countable_span_of_isCompl`.

## Implementation notes

The source builds a Kaplansky dévissage of `M` satisfying two extra conditions and then transports
it to `P` through Stacks 058W. Here the independent family of countably generated submodules of `P`
is produced directly, from the chain of traces of `P` on an increasing chain of `pr`-stable direct
summands of `M`, indexed by the well-ordered index set itself rather than by an ordinal:
`iSupIndep_and_iSup_eq_of_chain` below is the dévissage step, and no Kaplansky dévissage has to be
formed. This costs nothing in fidelity — the chain is the source's `(M_α)` reindexed — and avoids
the ordinal bookkeeping of Stacks 058U.

The mathematical content of the theorem is `inf_eq_sup_span_image_of_map_le`: the trace of `P` on a
`pr`-stable submodule `N'` is generated over its trace on a `pr`-stable `N ≤ N'` by the projections
of any generators of `N'` over `N`. It is what makes countability propagate from the chain in `M`
to the chain in `P`, and it is the only place where `pr` is used as more than a stability
condition.

The source's infinite matrix `(x_{mn})` is the closure of a single index under the map `f` above:
its rows are successive applications of `f`, and its anti-diagonal enumeration is exactly the
statement that the closure of a countable set under a countably-valued map is countable
(`exists_countable_closed`).

Six lemmas proved here are general facts about lattices with no dedicated Mathlib name, and are
stated in the generality in which they hold: `sup_inf_eq_of_codisjoint`,
`eq_of_disjoint_of_le_of_sup_eq` and `isCompl_inf_sup_of_isCompl` over a modular lattice, and
`isCompl_biSup_biSup_compl`, `iSupIndep_of_disjoint_biSup_lt` and `iSupIndep_and_iSup_eq_of_chain`
over a compactly generated modular lattice.

## References

* [Stacks 058X](https://stacks.math.columbia.edu/tag/058X)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372-377
-/

namespace Stacks.DirectSum.KaplanskySummand

open Submodule

/-! ### Lattice-theoretic preliminaries -/

/-- In a modular lattice, if `A ≤ B` and `A'` is codisjoint from `A`, then `B ⊓ A'` is a complement
of `A` inside `B`. -/
private lemma sup_inf_eq_of_codisjoint {α : Type*} [Lattice α] [OrderTop α] [IsModularLattice α]
    {A A' B : α} (h : Codisjoint A A') (hAB : A ≤ B) : A ⊔ B ⊓ A' = B := by
  rw [inf_comm B A', ← sup_inf_assoc_of_le A' hAB, h.eq_top, top_inf_eq]

/-- In a modular lattice, a subelement `C ≤ B` of an element disjoint from `A` and with the same
join with `A` is all of `B`. -/
lemma eq_of_disjoint_of_le_of_sup_eq {α : Type*} [Lattice α] [OrderBot α]
    [IsModularLattice α] {A B C : α} (hd : Disjoint A B) (hCB : C ≤ B) (h : A ⊔ C = A ⊔ B) :
    C = B :=
  calc C = C ⊔ A ⊓ B := by rw [hd.eq_bot, sup_bot_eq]
    _ = (C ⊔ A) ⊓ B := (sup_inf_assoc_of_le A hCB).symm
    _ = (A ⊔ B) ⊓ B := by rw [sup_comm C A, h]
    _ = B := inf_eq_right.2 le_sup_right

/-- If `A` and `A'` are disjoint, `N` and `N'` are complements, and `N` splits as
`(A ⊓ N) ⊔ (A' ⊓ N)`, then `(A' ⊓ N) ⊔ N'` is a complement of `A ⊓ N`. -/
@[sga "4 IV 9.1.13" "(c)"]
private lemma isCompl_inf_sup_of_isCompl {α : Type*} [Lattice α] [BoundedOrder α]
    [IsModularLattice α] {A A' N N' : α} (hA : Disjoint A A') (hN : IsCompl N N')
    (hsplit : (A ⊓ N) ⊔ (A' ⊓ N) = N) : IsCompl (A ⊓ N) ((A' ⊓ N) ⊔ N') := by
  have h1 : ((A' ⊓ N) ⊔ N') ⊓ N = A' ⊓ N := by
    rw [sup_inf_assoc_of_le N' (inf_le_right : A' ⊓ N ≤ N), inf_comm N' N,
      hN.disjoint.eq_bot, sup_bot_eq]
  refine ⟨disjoint_iff.2 (le_antisymm ?_ bot_le), codisjoint_iff.2 ?_⟩
  · calc (A ⊓ N) ⊓ ((A' ⊓ N) ⊔ N') = A ⊓ (N ⊓ ((A' ⊓ N) ⊔ N')) := inf_assoc A N _
      _ = A ⊓ (A' ⊓ N) := by rw [inf_comm N _, h1]
      _ ≤ A ⊓ A' := inf_le_inf_left A inf_le_left
      _ = ⊥ := hA.eq_bot
  · rw [← sup_assoc, hsplit, hN.sup_eq_top]

/-- In an independent family with supremum `⊤`, the partial supremum over a set of indices is a
direct summand, complemented by the partial supremum over the remaining indices. -/
private lemma isCompl_biSup_biSup_compl {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {ι : Type*} {A : ι → α} (hindep : iSupIndep A)
    (htop : ⨆ i, A i = ⊤) (J : Set ι) : IsCompl (⨆ i ∈ J, A i) (⨆ i ∈ Jᶜ, A i) := by
  refine ⟨hindep.disjoint_biSup_biSup disjoint_compl_right, codisjoint_iff.2 ?_⟩
  rw [← iSup_union, Set.union_compl_self, iSup_univ, htop]

/-- A family of elements of a compactly generated modular lattice, indexed by a linear order, is
independent as soon as each term is disjoint from the supremum of the earlier ones. -/
lemma iSupIndep_of_disjoint_biSup_lt {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {ι : Type*} [LinearOrder ι] {F : ι → α}
    (h : ∀ i, Disjoint (F i) (⨆ j < i, F j)) : iSupIndep F := by
  classical
  rw [iSupIndep_iff_supIndep]
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hm : s.max' hs ∈ s := s.max'_mem hs
      have hdis : Disjoint (F (s.max' hs)) ((s.erase (s.max' hs)).sup F) :=
        (h (s.max' hs)).mono_right <| Finset.sup_le fun j hj =>
          le_biSup F (lt_of_le_of_ne (s.le_max' j (Finset.mem_of_mem_erase hj))
            (Finset.ne_of_mem_erase hj))
      rw [← Finset.insert_erase hm]
      exact (ih _ (Finset.erase_ssubset hm)).insert hdis

/-- **The dévissage step.** Along a well-ordered index type, if `C i` is a complement of the
supremum of the earlier `F j` inside `F i`, then the `C i` are independent and have the same
supremum as the `F i`. This is the source's passage from a Kaplansky dévissage to a direct sum
decomposition, with the index type in place of an ordinal. -/
private lemma iSupIndep_and_iSup_eq_of_chain {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] {F C : ι → α}
    (hd : ∀ i, Disjoint (⨆ j < i, F j) (C i)) (hs : ∀ i, (⨆ j < i, F j) ⊔ C i = F i) :
    iSupIndep C ∧ ⨆ i, C i = ⨆ i, F i := by
  have hCF : ∀ i, C i ≤ F i := fun i => le_sup_right.trans_eq (hs i)
  refine ⟨iSupIndep_of_disjoint_biSup_lt fun i =>
      (hd i).symm.mono_right (iSup₂_mono fun j _ => hCF j),
    le_antisymm (iSup_mono hCF) (iSup_le fun i => ?_)⟩
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    rw [← hs i]
    exact sup_le (iSup₂_le fun j hj => ih j hj) (le_iSup C i)

/-! ### The closure of a set under a countably-valued map -/

/-- Any countable subset of `ι` is contained in a countable set closed under a countably-valued
map `f : ι → Set ι`. This is the source's infinite matrix `(x_{mn})`: the rows are the successive
images under `f`, and countability of the union is its enumeration along anti-diagonals. -/
private lemma exists_countable_closed {ι : Type*} (f : ι → Set ι) (hf : ∀ i, (f i).Countable)
    {J : Set ι} (hJ : J.Countable) :
    ∃ K : Set ι, J ⊆ K ∧ K.Countable ∧ ∀ i ∈ K, f i ⊆ K := by
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → Set ι, F 0 = J ∧ ∀ n, F (n + 1) = F n ∪ ⋃ i ∈ F n, f i :=
    ⟨fun n => Nat.rec J (fun _ s => s ∪ ⋃ i ∈ s, f i) n, rfl, fun _ => rfl⟩
  have hFc : ∀ n, (F n).Countable := by
    intro n
    induction n with
    | zero => rwa [hF0]
    | succ n ih =>
      rw [hFs n]
      exact ih.union (ih.biUnion fun i _ => hf i)
  refine ⟨⋃ n, F n, hF0 ▸ Set.subset_iUnion F 0, Set.countable_iUnion hFc, fun i hi => ?_⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hi
  refine subset_trans ?_ (Set.subset_iUnion F (n + 1))
  rw [hFs n]
  exact (Set.subset_biUnion_of_mem hn).trans Set.subset_union_right

/-- Over a linearly ordered index type, a countably-valued map `f` admits an increasing chain of
`f`-closed sets `V i` which is continuous and exhaustive, in the sense that `i ∈ V i` and the
partial union `⋃ j < i, V j` is again `f`-closed, and whose successive differences
`V i \ ⋃ j < i, V j` are countable. -/
private lemma exists_closed_chain {ι : Type*} [LinearOrder ι] (f : ι → Set ι)
    (hf : ∀ i, (f i).Countable) :
    ∃ V : ι → Set ι, Monotone V ∧ (∀ i, i ∈ V i) ∧ (∀ i, ∀ j ∈ V i, f j ⊆ V i) ∧
      (∀ i, ∀ j ∈ ⋃ k < i, V k, f j ⊆ ⋃ k < i, V k) ∧ (∀ i, (V i \ ⋃ j < i, V j).Countable) := by
  have hK : ∀ i, ∃ Ki : Set ι, i ∈ Ki ∧ Ki.Countable ∧ ∀ j ∈ Ki, f j ⊆ Ki := fun i => by
    obtain ⟨Ki, h1, h2, h3⟩ := exists_countable_closed f hf (Set.countable_singleton i)
    exact ⟨Ki, h1 rfl, h2, h3⟩
  choose K hKmem hKc hKcl using hK
  have hsub : ∀ i j, j ≤ i → K j ⊆ ⋃ k ≤ i, K k := fun i j hj x hx =>
    Set.mem_iUnion₂.2 ⟨j, hj, hx⟩
  refine ⟨fun i => ⋃ j ≤ i, K j,
    fun a b hab => Set.iUnion₂_subset fun j hj => hsub b j (hj.trans hab),
    fun i => hsub i i le_rfl (hKmem i), ?_, ?_, ?_⟩
  · intro i j hj
    obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.1 hj
    exact (hKcl k j hjk).trans (hsub i k hk)
  · intro i j hj
    obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.1 hj
    obtain ⟨l, hl, hjl⟩ := Set.mem_iUnion₂.1 hjk
    exact (hKcl l j hjl).trans fun x hx =>
      Set.mem_iUnion₂.2 ⟨l, hl.trans_lt hk, hsub l l le_rfl hx⟩
  · refine fun i => (hKc i).mono fun x hx => ?_
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx.1
    rcases eq_or_lt_of_le hj with rfl | hji
    · exact hxj
    · exact absurd (Set.mem_iUnion₂.2 ⟨j, hji, hsub j j le_rfl hxj⟩) hx.2

/-! ### Traces of a direct summand on a stable submodule -/

/-- A submodule stable under a projection `pr` onto `P` whose kernel lies in `Q` is the sum of its
traces on `P` and on `Q`. -/
private lemma inf_sup_inf_eq_of_map_le {R : Type*} {M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {P Q : Submodule R M} {pr : M →ₗ[R] M} (hP : ∀ x, pr x ∈ P)
    (hQ : ∀ x, x - pr x ∈ Q) {N : Submodule R M} (hN : N.map pr ≤ N) :
    (P ⊓ N) ⊔ (Q ⊓ N) = N := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
  have h1 : pr x ∈ P ⊓ N := mem_inf.2 ⟨hP x, hN (mem_map_of_mem hx)⟩
  simpa using add_mem_sup h1 (mem_inf.2 ⟨hQ x, sub_mem hx (mem_inf.1 h1).2⟩)

/-- **Kaplansky's step.** Let `pr` be a projection of `M` onto `P` and let `N ≤ N'` be submodules
stable under `pr`, with `N'` generated over `N` by a set `W`. Then the trace of `P` on `N'` is
generated over the trace of `P` on `N` by the *projections* of the elements of `W`.

This is the mathematical content of the theorem: it says that the chain of traces of `P` has
successive quotients generated by no more elements than the original chain, so that countability
propagates from `M` to `P`. -/
private lemma inf_eq_sup_span_image_of_map_le {R : Type*} {M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {P : Submodule R M} {pr : M →ₗ[R] M} (hpr : LinearMap.IsProj P pr)
    {N N' : Submodule R M} (hN : N.map pr ≤ N) (hN' : N'.map pr ≤ N') {W : Set M}
    (hW : N' = N ⊔ span R W) : P ⊓ N' = (P ⊓ N) ⊔ span R (pr '' W) := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (inf_le_inf_left P (le_sup_left.trans hW.ge)) (span_le.2 ?_))
  · obtain ⟨hxP, hxN⟩ := mem_inf.1 hx
    rw [hW] at hxN
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hxN
    rw [← hpr.map_id _ hxP, map_add]
    exact add_mem_sup (mem_inf.2 ⟨hpr.map_mem a, hN (mem_map_of_mem ha)⟩)
      ((Submodule.map_span pr W).le (mem_map_of_mem hb))
  · rintro _ ⟨y, hy, rfl⟩
    exact mem_inf.2 ⟨hpr.map_mem y,
      hN' (mem_map_of_mem (hW.ge (Submodule.mem_sup_right (subset_span hy))))⟩

/-- If `C` is a complement of `A` inside `A ⊔ span R t`, then `C` is spanned by the components in
`C` of the elements of `t`; in particular `C` is countably generated when `t` is countable. -/
private lemma exists_countable_span_eq_of_disjoint {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {A C : Submodule R M} {t : Set M} (ht : t.Countable)
    (hd : Disjoint A C) (h : A ⊔ C = A ⊔ span R t) :
    ∃ t' : Set M, t'.Countable ∧ span R t' = C := by
  have hmem : ∀ x ∈ t, ∃ y ∈ A, ∃ z ∈ C, y + z = x := by
    intro x hx
    rw [← Submodule.mem_sup, h]
    exact Submodule.mem_sup_right (subset_span hx)
  choose! a ha c hc hac using hmem
  refine ⟨c '' t, ht.image c, ?_⟩
  have hle : span R (c '' t) ≤ C := span_le.2 (Set.image_subset_iff.2 hc)
  refine eq_of_disjoint_of_le_of_sup_eq hd hle
    (le_antisymm (sup_le_sup_left hle A) (h.trans_le (sup_le le_sup_left (span_le.2 ?_))))
  intro x hx
  have hx' : a x + c x ∈ A ⊔ span R (c '' t) :=
    add_mem_sup (ha x hx) (subset_span ⟨x, hx, rfl⟩)
  rwa [hac x hx] at hx'

/-- Let `pr` be the projection onto `P` along `Q`, and let `N ≤ N'` be submodules stable under `pr`
with `N` a direct summand of `M` and `N'` generated over `N` by a countable set. Then the trace of
`P` on `N` has a countably generated complement inside the trace of `P` on `N'`. These complements
are the terms of the dévissage of `P`. -/
private lemma exists_countable_span_inf_of_map_le {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {P Q : Submodule R M} (hPQ : Disjoint P Q) {pr : M →ₗ[R] M}
    (hpr : LinearMap.IsProj P pr) (hprQ : ∀ x, x - pr x ∈ Q) {N N' X : Submodule R M}
    (hX : IsCompl N X) (hN : N.map pr ≤ N) (hN' : N'.map pr ≤ N') {W : Set M}
    (hWc : W.Countable) (hW : N' = N ⊔ span R W) :
    ∃ C : Submodule R M, Disjoint (P ⊓ N) C ∧ (P ⊓ N) ⊔ C = P ⊓ N' ∧
      ∃ t : Set M, t.Countable ∧ span R t = C := by
  have hcompl : IsCompl (P ⊓ N) ((Q ⊓ N) ⊔ X) :=
    isCompl_inf_sup_of_isCompl hPQ hX (inf_sup_inf_eq_of_map_le hpr.map_mem hprQ hN)
  have hsup : (P ⊓ N) ⊔ (P ⊓ N') ⊓ ((Q ⊓ N) ⊔ X) = P ⊓ N' :=
    sup_inf_eq_of_codisjoint hcompl.codisjoint (inf_le_inf_left P (le_sup_left.trans hW.ge))
  have hdisj : Disjoint (P ⊓ N) ((P ⊓ N') ⊓ ((Q ⊓ N) ⊔ X)) :=
    hcompl.disjoint.mono_right inf_le_right
  exact ⟨_, hdisj, hsup, exists_countable_span_eq_of_disjoint (hWc.image pr) hdisj
    (hsup.trans (inf_eq_sup_span_image_of_map_le hpr hN hN' hW))⟩

/-- Choose generators `g i` of each `A i` and, for each `x : M`, a set `supp x` of indices with
`x ∈ ⨆ i ∈ supp x, A i`. If a set `J` of indices contains the support of `pr x` for every generator
`x` of every `A j` with `j ∈ J`, then `⨆ j ∈ J, A j` is stable under `pr`. -/
private lemma map_biSup_le_of_forall_support_subset {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {ι : Type*} {A : ι → Submodule R M} {g : ι → Set M}
    (hgs : ∀ i, span R (g i) = A i) {pr : M →ₗ[R] M} {supp : M → Set ι}
    (hsupp : ∀ x, x ∈ ⨆ i ∈ supp x, A i) {J : Set ι}
    (hJ : ∀ j ∈ J, ∀ x ∈ g j, supp (pr x) ⊆ J) : (⨆ j ∈ J, A j).map pr ≤ ⨆ j ∈ J, A j := by
  simp only [Submodule.map_iSup]
  refine iSup₂_le fun j hj => ?_
  rw [← hgs j, Submodule.map_span]
  refine span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact SetLike.mem_coe.2 (iSup_le_iSup_of_subset (f := A) (hJ j hj x hx) (hsupp (pr x)))

/-! ### Passing from submodules of `M` contained in `P` to submodules of `↥P` -/

/-- An independent family of countably generated submodules of `M` with supremum `P` gives an
independent set of countably generated submodules of `↥P` with supremum `⊤`. -/
private lemma exists_sSupIndep_countable_span_subtype {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {P : Submodule R M} {ι : Type*} {C : ι → Submodule R M}
    (hle : ∀ i, C i ≤ P) (hindep : iSupIndep C) (hsup : ⨆ i, C i = P)
    (hcount : ∀ i, ∃ t : Set M, t.Countable ∧ span R t = C i) :
    ∃ S : Set (Submodule R ↥P), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ T ∈ S, ∃ t : Set ↥P, t.Countable ∧ span R t = T := by
  have hinj : Function.Injective P.subtype := P.injective_subtype
  have hmapinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective hinj
  have hmap : ∀ i, ((C i).comap P.subtype).map P.subtype = C i := fun i => by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (hle i)]
  have hdisj : ∀ X Y : Submodule R ↥P,
      Disjoint (X.map P.subtype) (Y.map P.subtype) → Disjoint X Y := fun X Y h => by
    rw [disjoint_iff] at h ⊢
    exact hmapinj (by rw [Submodule.map_inf _ hinj, h, Submodule.map_bot])
  have hindepD : iSupIndep fun i => (C i).comap P.subtype := fun i =>
    hdisj _ _ (by simpa only [Submodule.map_iSup, hmap] using hindep i)
  refine ⟨Set.range fun i => (C i).comap P.subtype, hindepD.sSupIndep_range, ?_, ?_⟩
  · rw [sSup_range]
    refine hmapinj ?_
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
    simpa only [hmap] using hsup
  · rintro T ⟨i, rfl⟩
    obtain ⟨t, htc, hts⟩ := hcount i
    have htP : t ⊆ Set.range P.subtype := fun x hx =>
      ⟨⟨x, hle i (hts ▸ Submodule.subset_span hx)⟩, rfl⟩
    refine ⟨P.subtype ⁻¹' t, htc.preimage hinj, hmapinj ?_⟩
    rw [hmap, Submodule.map_span, Set.image_preimage_eq_of_subset htP, hts]

/-! ### The main construction -/

/-- The dévissage of `P` along a chain in `M`. Let `pr` be the projection onto `P` along `Q` and
let `N` be an increasing chain of submodules of `M`, indexed by a well-ordered type, with supremum
`⊤`, such that each `N i` and each partial supremum `⨆ j < i, N j` is stable under `pr`, the latter
is a direct summand of `M`, and `N i` is generated over it by a countable set. Then `P` is a direct
sum of countably generated submodules. -/
private lemma exists_sSupIndep_countable_span_of_chain {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {P Q : Submodule R M} (hPQ : Disjoint P Q) {pr : M →ₗ[R] M}
    (hpr : LinearMap.IsProj P pr) (hprQ : ∀ x, x - pr x ∈ Q) {ι : Type*} [LinearOrder ι]
    [WellFoundedLT ι] (N : ι → Submodule R M) (hmono : Monotone N) (htop : ⨆ i, N i = ⊤)
    (hstable : ∀ i, (N i).map pr ≤ N i)
    (hstable' : ∀ i, (⨆ j < i, N j).map pr ≤ ⨆ j < i, N j)
    (hsummand : ∀ i, ∃ X, IsCompl (⨆ j < i, N j) X)
    (hcount : ∀ i, ∃ W : Set M, W.Countable ∧ N i = (⨆ j < i, N j) ⊔ span R W) :
    ∃ S : Set (Submodule R ↥P), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ T ∈ S, ∃ t : Set ↥P, t.Countable ∧ span R t = T := by
  have hdirlt : ∀ i : ι, Directed (· ≤ ·) fun j : {j : ι // j < i} => N j := fun i a b =>
    (le_total (a : ι) (b : ι)).elim (fun h => ⟨b, hmono h, le_rfl⟩) fun h => ⟨a, le_rfl, hmono h⟩
  have hE : ∀ i, (⨆ j < i, P ⊓ N j) = P ⊓ ⨆ j < i, N j := fun i => by
    rw [iSup_subtype', iSup_subtype']
    exact ((hdirlt i).inf_iSup_eq).symm
  have hstep : ∀ i, ∃ C : Submodule R M, Disjoint (⨆ j < i, P ⊓ N j) C ∧
      (⨆ j < i, P ⊓ N j) ⊔ C = P ⊓ N i ∧ ∃ t : Set M, t.Countable ∧ span R t = C := by
    intro i
    obtain ⟨X, hX⟩ := hsummand i
    obtain ⟨W, hWc, hW⟩ := hcount i
    rw [hE i]
    exact exists_countable_span_inf_of_map_le hPQ hpr hprQ hX (hstable' i) (hstable i) hWc hW
  choose C hCd hCs hCc using hstep
  obtain ⟨hindep, hCsup⟩ := iSupIndep_and_iSup_eq_of_chain (F := fun i => P ⊓ N i) hCd hCs
  refine exists_sSupIndep_countable_span_subtype
    (fun i => (le_sup_right.trans_eq (hCs i)).trans inf_le_left) hindep ?_ hCc
  rw [hCsup, ← Directed.inf_iSup_eq hmono.directed_le, htop, inf_top_eq]

/-- Stacks 058X for a decomposition of `M` indexed by a well-ordered type: the chain of closed sets
of indices produced by `exists_closed_chain` gives the chain of submodules that
`exists_sSupIndep_countable_span_of_chain` needs. -/
private lemma exists_sSupIndep_countable_span_of_wellOrder {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    (A : ι → Submodule R M) (hAindep : iSupIndep A) (hAtop : ⨆ i, A i = ⊤)
    (hAcount : ∀ i, ∃ t : Set M, t.Countable ∧ span R t = A i) {P Q : Submodule R M}
    (hPQ : Disjoint P Q) {pr : M →ₗ[R] M} (hpr : LinearMap.IsProj P pr)
    (hprQ : ∀ x, x - pr x ∈ Q) :
    ∃ S : Set (Submodule R ↥P), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ T ∈ S, ∃ t : Set ↥P, t.Countable ∧ span R t = T := by
  classical
  choose g hgc hgs using hAcount
  have hsuppex : ∀ x : M, ∃ s : Set ι, s.Countable ∧ x ∈ ⨆ i ∈ s, A i := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1
      (hAtop.ge Submodule.mem_top : x ∈ ⨆ i, A i)
    exact ⟨↑s, s.countable_toSet, by simpa using hs⟩
  choose supp hsuppc hsuppmem using hsuppex
  obtain ⟨V, hVmono, hVmem, hVcl, hUcl, hVdiff⟩ :=
    exists_closed_chain (fun i => ⋃ x ∈ g i, supp (pr x))
      fun i => (hgc i).biUnion fun x _ => hsuppc (pr x)
  have hUeq : ∀ i, (⨆ j < i, ⨆ l ∈ V j, A l) = ⨆ j ∈ ⋃ k < i, V k, A j := fun i => by
    simp only [iSup_iUnion]
  have hmono : Monotone fun i => ⨆ j ∈ V i, A j := fun a b hab =>
    iSup_le_iSup_of_subset (hVmono hab)
  have htop : (⨆ i, ⨆ j ∈ V i, A j) = ⊤ :=
    le_antisymm le_top (hAtop.ge.trans (iSup_le fun i =>
      (le_biSup A (hVmem i)).trans (le_iSup (fun k => ⨆ j ∈ V k, A j) i)))
  have hstab : ∀ J : Set ι, (∀ j ∈ J, (⋃ x ∈ g j, supp (pr x)) ⊆ J) →
      (⨆ j ∈ J, A j).map pr ≤ ⨆ j ∈ J, A j := fun J hJ =>
    map_biSup_le_of_forall_support_subset hgs hsuppmem fun j hj x hx =>
      (Set.subset_biUnion_of_mem (u := fun y => supp (pr y)) hx).trans (hJ j hj)
  have hstable : ∀ i, (⨆ j ∈ V i, A j).map pr ≤ ⨆ j ∈ V i, A j := fun i => hstab _ (hVcl i)
  have hstable' : ∀ i, (⨆ j < i, ⨆ l ∈ V j, A l).map pr ≤ ⨆ j < i, ⨆ l ∈ V j, A l := fun i => by
    rw [hUeq i]
    exact hstab _ (hUcl i)
  have hsummand : ∀ i, ∃ X, IsCompl (⨆ j < i, ⨆ l ∈ V j, A l) X := fun i => by
    rw [hUeq i]
    exact ⟨_, isCompl_biSup_biSup_compl hAindep hAtop _⟩
  have hcount : ∀ i, ∃ W : Set M, W.Countable ∧
      (⨆ j ∈ V i, A j) = (⨆ j < i, ⨆ l ∈ V j, A l) ⊔ span R W := fun i =>
    ⟨⋃ j ∈ V i \ ⋃ k < i, V k, g j, (hVdiff i).biUnion fun j _ => hgc j, by
      rw [hUeq i, Submodule.span_iUnion₂]
      simp only [hgs]
      rw [← iSup_union, Set.union_sdiff_cancel (Set.iUnion₂_subset fun k hk => hVmono hk.le)]⟩
  exact exists_sSupIndep_countable_span_of_chain hPQ hpr hprQ _ hmono htop hstable hstable'
    hsummand hcount

/-- **Stacks 058X.** Let `M` be a module over a ring `R` which is a direct sum of countably
generated `R`-modules. If `P` is a direct summand of `M`, with complement `Q`, then `P` is also a
direct sum of countably generated `R`-modules. -/
public theorem solution {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M]
    (hM : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ span R t = N)
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    ∃ S : Set (Submodule R ↥P), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set ↥P, t.Countable ∧ span R t = N := by
  obtain ⟨S, hSindep, hStop, hScount⟩ := hM
  -- a well-ordered copy of the index set of the given decomposition
  obtain ⟨e⟩ : Nonempty (↥S ≃ (Cardinal.mk ↥S).ord.ToType) :=
    Cardinal.eq.mp (Cardinal.mk_ord_toType _).symm
  refine exists_sSupIndep_countable_span_of_wellOrder (fun i => (e.symm i : Submodule R M))
    (((sSupIndep_iff S).1 hSindep).comp e.symm.injective) ?_
    (fun i => hScount _ (e.symm i).2) hPQ.disjoint
    ⟨Submodule.projection_apply_mem hPQ, fun x hx => Submodule.projection_apply_left hPQ ⟨x, hx⟩⟩
    (Submodule.sub_projection_mem hPQ)
  rw [← hStop, sSup_eq_iSup']
  exact e.symm.iSup_comp (g := fun j : ↥S => (j : Submodule R M))

end Stacks.DirectSum.KaplanskySummand

/-!
# Direct summands of direct sums of countably generated modules

Let `M` be a module over a ring `R` which is a direct sum of countably generated `R`-modules, and
let `P` be a direct summand of `M`. Then `P` is again a direct sum of countably generated
`R`-modules. This is Kaplansky's theorem that being a direct sum of countably generated modules
passes to direct summands; combined with the fact that a projective module is a direct summand of a
free module, and that a free module is a direct sum of copies of `R`, it gives Kaplansky's
decomposition of a projective module as a direct sum of countably generated projective modules
(Stacks 058Y), and through it the reduction of the freeness of projective modules to the countably
generated case (Stacks 0590). The proof of the source constructs, for a decomposition `M = P ⊕ Q`,
a Kaplansky dévissage `(M_α)` of `M` (Stacks 058U) each of whose terms is a direct summand of `M`
and splits as `M_α = (P ∩ M_α) ⊕ (Q ∩ M_α)`, so that the traces `P ∩ M_α` form a Kaplansky
dévissage of `P`, which by Stacks 058W is a direct sum of countably generated modules.

## Main results

* `Submodule.exists_sSupIndep_countable_span_of_isCompl`: a direct summand of a direct sum of
  countably generated `R`-modules is a direct sum of countably generated `R`-modules.

## Implementation notes

"Is a direct sum of countably generated `R`-modules" is spelled internally, exactly as in
Stacks 058W: the existence of a set `S` of submodules which is independent (`sSupIndep`) and has
supremum `⊤`, each member of which is spanned by a countable set. Independence together with
`sSup S = ⊤` says that the canonical map `⨁ N : S, N → M` is an isomorphism, by `sSupIndep_iff` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, and conversely the images of the
summands under an isomorphism `M ≅ ⨁_{i ∈ I} N_i` form such a set. So the hypothesis here is
literally the left hand side of Stacks 058W at `M`, and the conclusion is literally that same
condition at the module `↥P`; either one may therefore be traded for a Kaplansky dévissage.

The conclusion is stated by submodules of `↥P` with supremum `⊤`, rather than by submodules of `M`
with supremum `P`, so that it is the same predicate as the hypothesis and not a relative variant of
it. The two forms correspond along the order isomorphism `Submodule.mapIic P` between the
submodules of `↥P` and the submodules of `M` below `P`, which preserves disjointness, suprema and
countable generation, and it is the `⊤` form that Mathlib's internal direct sum API is phrased for.

Being a direct summand is written as `IsCompl P Q` for a named complement `Q`, the source's
`M = P ⊕ Q`: quantifying over `Q` says the same thing as asserting the existence of one, and the
complement is what the proof works with. It is a complement in the lattice of submodules of `M`,
the form in which the dévissage of Stacks 058U states its splittings.

The source's commutative ring is weakened to a ring; commutativity is nowhere used. Additive
inverses are not slack: over a semiring `Disjoint P Q` with `P ⊔ Q = ⊤` does not make `M` the
direct sum of `P` and `Q` (for `R = ℕ` and `M = ℕ∞` take `P = {0, ⊤}` and `Q = ℕ`, where
`⊤ = ⊤ + 0 = ⊤ + 1`), so over a semiring neither the hypothesis nor the summand condition would say
what the source means.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead. Dropping `hM` is false: `R = ℤ` and `M = P = ℤ^ℕ` with `Q = ⊥` satisfies
`IsCompl P Q`, while the Baer–Specker group is not a direct sum of countably generated groups,
since its countable subgroups are free (it is `ℵ₁`-free) and a direct sum of free groups is free,
which Specker's theorem forbids. Dropping the summand hypothesis to "`P` is a submodule of `M`" is
false as well: over `ℤ` the group `M = ℚ^ℕ` is a `ℚ`-vector space, hence a direct sum of copies of
`ℚ`, each countably generated over `ℤ`, and it contains `P = ℤ^ℕ`, which is not such a direct sum
by the previous sentence (and is indeed not a summand, `ℚ^ℕ` being divisible).
(2) The scalars and the base are the source's: `S` and the summands of `P` are `R`-submodules, the
complement `Q` is an `R`-submodule of the same `M`, and every generating set spans over `R`, `↥P`
carrying its induced `R`-module structure; nothing is localized or base changed.
(3) The source names no canonical map, and what is pinned instead is internal to `M` and to `P`:
the decomposition of `M` is an independent set of submodules of `M` with supremum `⊤`, the summand
relation is `IsCompl` in the submodule lattice of `M`, and the decomposition of `P` is by
submodules of `P` itself, not merely an abstract isomorphism of `P` onto a direct sum of countably
generated modules.
(4) The instantiation is not degenerate: for `R` a field and `M` a vector space of uncountable
dimension, the set of lines through a basis witnesses the hypothesis, every subspace `P` has a
complement, and the conclusion holds nontrivially with an uncountable set of summands; taking `P`
the image of an idempotent endomorphism of a free module of uncountable rank which is not the
projection onto a subfamily of coordinates gives an instance whose conclusion is not read off the
given decomposition, which is the content of the theorem.

## References

* [Stacks 058X](https://stacks.math.columbia.edu/tag/058X)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372–377
-/

@[expose] public section

namespace Submodule

/-- **Stacks 058X.** Let `M` be a module over a ring `R` which is a direct sum of countably
generated `R`-modules — that is, `M` is the internal direct sum of an independent set of countably
generated submodules. If `P` is a direct summand of `M`, with complement `Q`, then `P` is also a
direct sum of countably generated `R`-modules. -/
@[stacks 058X "Being a direct sum of countably generated modules written internally, as in 058W:
  an independent set of submodules with supremum `⊤`, each spanned by a countable set. `P` is a
  direct summand of `M` in the sense of a complement in the submodule lattice of `M`."]
public theorem exists_sSupIndep_countable_span_of_isCompl {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    (hM : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ span R t = N)
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    ∃ S : Set (Submodule R ↥P), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set ↥P, t.Countable ∧ span R t = N :=
  Stacks.DirectSum.KaplanskySummand.solution (M := M) hM P Q hPQ

end Submodule

end
