module

import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan

@[expose] public section

/-!
# Regular sequences are quasi-regular

The multi-index power `listPow`, the elementary form `IsQuasiregularSeq` of quasi-regularity, the
cons and snoc induction steps, and the main results `isRegular_isQuasiregularSeq` (Stacks 00LN (2))
and `isRegular_isQuasiregularSeq_self` (Stacks 00LN (1)).
-/

@[expose] public section

open scoped Finset

namespace Stacks.QuasiregularSequence

variable {R : Type*} [CommRing R]

/-- `f^I = ∏ i, (rs[i])^(I i)` for a multi-index `I : Fin rs.length → ℕ`. -/
def listPow (rs : List R) (I : Fin rs.length → ℕ) : R :=
  ∏ i, rs[i] ^ I i

/-- **Definition 3 (reformulated).** The sequence `rs` is an *`M`-quasi-regular
sequence* if, for every total degree `n` and every family `(m_I)_{|I| = n}` of
elements of `M`, a relation `∑_{|I| = n} f^I m_I ∈ J^{n+1} M` forces `m_I ∈ J M`
for all `I` with `|I| = n`. This is the degree-wise injectivity of the canonical
comparison map `Φ_M` of Definition 2 (which is always surjective), and hence is
equivalent to `Φ_M` being an isomorphism. -/
@[ega "0 15.1.4" "more general"]
def IsQuasiregularSeq (rs : List R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (n : ℕ) (m : (Fin rs.length → ℕ) → M),
    (∑ I ∈ Finset.Nat.antidiagonalTuple rs.length n, listPow rs I • m I) ∈
        (Ideal.ofList rs ^ (n + 1)) • (⊤ : Submodule R M) →
      ∀ I ∈ Finset.Nat.antidiagonalTuple rs.length n, m I ∈ (Ideal.ofList rs) • (⊤ : Submodule R M)

/-! ## Main statements -/

open RingTheory.Sequence

/-- The empty sequence is quasi-regular: only `n = 0` contributes, the unique
multi-index is the empty tuple, `f^∅ = 1`, and `J = (∅) = ⊥`, so the relation
`m_∅ ∈ ⊥` forces `m_∅ = 0 ∈ ⊥ • ⊤`. -/
theorem isQuasiregularSeq_nil (M : Type*) [AddCommGroup M] [Module R M] :
    IsQuasiregularSeq ([] : List R) M := by
  intro n m hsum I hI
  have hofl : Ideal.ofList ([] : List R) = ⊥ := by simp [Ideal.ofList]
  rw [Finset.Nat.mem_antidiagonalTuple] at hI
  have hn : n = 0 := by
    rw [← hI]
    exact Finset.sum_eq_zero fun i _ => i.elim0
  subst hn
  rw [hofl, Submodule.bot_smul, Submodule.mem_bot]
  rw [show Finset.Nat.antidiagonalTuple [].length 0 = {0} from
      Finset.Nat.antidiagonalTuple_zero_right _,
    Finset.sum_singleton] at hsum
  rw [hofl, show (⊥ : Ideal R) ^ (0 + 1) = ⊥ by simp, Submodule.bot_smul, Submodule.mem_bot,
    listPow, Finset.prod_eq_one (fun i _ => i.elim0), one_smul] at hsum
  obtain rfl : I = 0 := funext fun i => i.elim0
  exact hsum

/-! ## The cons step

Notation throughout: `J = Ideal.ofList (f :: gs)`, `J' = Ideal.ofList gs`,
`g^{I'} = listPow gs I'`.  A multi-index `I : Fin (gs.length + 1) → ℕ` for the
sequence `f :: gs` decomposes as `(a, I')` where `a = I 0` is the exponent of `f`
and `I' = I ∘ Fin.succ` is the restriction to `gs`.  Then
`listPow (f :: gs) I = f ^ a * listPow gs I'`, which is `listPow_cons` below.
-/

/-- A power `f^I` for the sequence `f :: gs` factors as `f^(I 0)` times the power
for `gs` on the shifted index.  This is the basic bookkeeping identity behind the
whole cons step. -/
theorem listPow_cons (f : R) (gs : List R) (I : Fin (gs.length + 1) → ℕ) :
    listPow (f :: gs) I = f ^ I 0 * listPow gs (fun i => I i.succ) := by
  change
    (∏ i : Fin (gs.length + 1), (f :: gs)[i] ^ I i) =
      f ^ I 0 * ∏ i : Fin gs.length, gs[i] ^ I i.succ
  rw [Fin.prod_univ_succ]
  rfl

/-- Ideal decomposition: `(f :: gs) = (f) + (gs)` at the level of generated ideals.
It follows from `{r | r ∈ f :: gs} = insert f {r | r ∈ gs}` and
`Ideal.span_insert`. -/
theorem ofList_cons_sup (f : R) (gs : List R) :
    Ideal.ofList (f :: gs) = Ideal.span {f} ⊔ Ideal.ofList gs := by
  unfold Ideal.ofList
  rw [show {r | r ∈ f :: gs} = insert f {r | r ∈ gs} by ext; simp, Ideal.span_insert]

open scoped Pointwise in
/-- **Reduction modulo `f`.**
If the degree-`n` relation `∑_{|I| = n} listPow (f::gs) I • m I` lies in
`J^{n+1} M`, then every coefficient `m I` whose `f`-exponent is `0`
(i.e. `I 0 = 0`) already lies in `J M`.

The argument uses only the tail hypothesis `hgs`.
Let `π : M → Mbar := QuotSMulTop f M = M ⧸ f • ⊤` be the quotient map; recall
`f • (⊤ : Submodule R Mbar) = ⊥`, i.e. `f` annihilates `Mbar`.

* (Kill the `a ≥ 1` terms.) Apply `π` to the relation. By `listPow_cons` each
  term is `f^(I 0) • (listPow gs (I∘succ) • m I)`; for `I 0 ≥ 1` this is in
  `f • ⊤`, hence `π` sends it to `0`. So the image of the LHS is
  `∑_{|I'| = n} listPow gs I' • π (m (Fin.cons 0 I'))`, a degree-`n` relation for
  `gs` on `Mbar`, where `I'` ranges over `antidiagonalTuple gs.length n` and we
  pair it with the index `Fin.cons 0 I'` (first coordinate `0`).
  (Indexing: the indices `I` of `antidiagonalTuple (gs.length+1) n` with `I 0 = 0`
  are exactly `Fin.cons 0 I'` for `I' ∈ antidiagonalTuple gs.length n`, the "peel
  first coordinate" decomposition of `antidiagonalTuple`.)

* (Track the right-hand side.) `J = (f) ⊔ J'` (lemma `ofList_cons_sup`), so
  modulo `f` we have `J • ⊤ ↦ J' • ⊤` on `Mbar`, and consequently
  `J^{n+1} • ⊤ ↦ (J')^{n+1} • ⊤` on `Mbar`.  Hence the image relation lies in
  `(Ideal.ofList gs)^{n+1} • (⊤ : Submodule R Mbar)`.

* (Apply tail quasi-regularity.) The pushed-down data is exactly the hypothesis
  of `hgs` at degree `n` for the family `m̄ I' := π (m (Fin.cons 0 I'))`.  Thus
  `hgs` gives `π (m (Fin.cons 0 I')) ∈ (Ideal.ofList gs) • ⊤` for all `|I'| = n`.

* (Lift back.) `π (m (Fin.cons 0 I')) ∈ J' • ⊤_Mbar` means
  `m (Fin.cons 0 I') ∈ J' • ⊤ + f • ⊤ = J • ⊤` (using `ofList_cons_sup` and
  `sup_smul`/`Submodule.add_smul`-style facts).  Since any `I` with `I 0 = 0`
  equals `Fin.cons 0 (I∘succ)`, this is the claim. -/
theorem cons_reduce_mod_f (M : Type*) [AddCommGroup M] [Module R M] (f : R) (gs : List R)
    (hgs : IsQuasiregularSeq gs (QuotSMulTop f M)) (n : ℕ) (m : (Fin (gs.length + 1) → ℕ) → M)
    (hsum :
      (∑ I ∈ Finset.Nat.antidiagonalTuple (gs.length + 1) n, listPow (f :: gs) I • m I) ∈
        (Ideal.ofList (f :: gs) ^ (n + 1)) • (⊤ : Submodule R M))
    (I : Fin (gs.length + 1) → ℕ) (hI : I ∈ Finset.Nat.antidiagonalTuple (gs.length + 1) n)
    (hI0 : I 0 = 0) : m I ∈ (Ideal.ofList (f :: gs)) • (⊤ : Submodule R M) := by
  set π := (Submodule.mkQ (f • ⊤ : Submodule R M)) with hπ
  have hfann : ∀ x : QuotSMulTop f M, f • x = 0 :=
    Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M f)
  have hcons : ∀ (J : Fin (gs.length + 1) → ℕ), J 0 = 0 → Fin.cons 0 (fun j => J j.succ) = J := by
    intro J h
    funext i
    exact Fin.cases (by simp [h]) (fun j => by simp) i
  set mbar : (Fin gs.length → ℕ) → QuotSMulTop f M := fun J => π (m (Fin.cons 0 J)) with hmbar
  have key :
    π (∑ K ∈ Finset.Nat.antidiagonalTuple (gs.length + 1) n, listPow (f :: gs) K • m K) =
      ∑ J ∈ Finset.Nat.antidiagonalTuple gs.length n, listPow gs J • mbar J := by
    rw [map_sum]
    rw [← Finset.sum_filter_of_ne (p := fun K => K 0 = 0)]
    · apply Finset.sum_nbij' (i := fun K => fun j => K j.succ) (j := fun J => Fin.cons 0 J)
      · intro K hK
        rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hK
        rw [Finset.Nat.mem_antidiagonalTuple]
        have hs : ∑ i, K i = n := hK.left
        rwa [Fin.sum_univ_succ, hK.right, zero_add] at hs
      · intro J hJ
        rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
        rw [Finset.Nat.mem_antidiagonalTuple] at hJ
        refine ⟨?_, by simp⟩
        rw [Fin.sum_univ_succ]; simp [hJ]
      · intro K hK
        rw [Finset.mem_filter] at hK; exact hcons K hK.right
      · intro J hJ; funext j; simp
      · intro K hK
        rw [Finset.mem_filter] at hK
        rw [map_smul, listPow_cons, hK.right, pow_zero, one_mul]
        simp only [hmbar, hcons K hK.right]
    · intro K hK hK0
      by_contra hne
      apply hK0
      rw [map_smul, listPow_cons]
      have hfac : f ^ K 0 = f * f ^ (K 0 - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)]
      rw [hfac, mul_assoc, mul_smul]
      exact hfann _
  have hpow :
    ∀ k,
      (Ideal.ofList (f :: gs)) ^ k • (⊤ : Submodule R (QuotSMulTop f M)) =
        (Ideal.ofList gs) ^ k • (⊤ : Submodule R (QuotSMulTop f M)) := by
    have hspan : (Ideal.span {f}) • (⊤ : Submodule R (QuotSMulTop f M)) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      intro r hr x _
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨c, rfl⟩ := hr
      rw [mul_comm, mul_smul, hfann]; simp
    have hJX :
      ∀ X : Submodule R (QuotSMulTop f M),
        (Ideal.ofList (f :: gs)) • X = (Ideal.ofList gs) • X := by
      intro X
      rw [ofList_cons_sup, Submodule.sup_smul]
      rw [le_bot_iff.mp ((Submodule.smul_mono le_rfl le_top).trans hspan.le), bot_sup_eq]
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, hJX, ih]
  have hgssum :
    (∑ J ∈ Finset.Nat.antidiagonalTuple gs.length n, listPow gs J • mbar J) ∈
      (Ideal.ofList gs ^ (n + 1)) • (⊤ : Submodule R (QuotSMulTop f M)) := by
    rw [← key, ← hpow]
    have hmem :
      π (∑ K ∈ Finset.Nat.antidiagonalTuple (gs.length + 1) n, listPow (f :: gs) K • m K) ∈
        Submodule.map π ((Ideal.ofList (f :: gs) ^ (n + 1)) • ⊤) :=
      Submodule.mem_map_of_mem hsum
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmem
  have happ :=
    hgs n mbar hgssum (fun i => I i.succ)
      (by
        rw [Finset.Nat.mem_antidiagonalTuple]
        rw [Finset.Nat.mem_antidiagonalTuple] at hI
        have hs : ∑ i, I i = n := hI
        rwa [Fin.sum_univ_succ, hI0, zero_add] at hs)
  simp only [hmbar] at happ
  rw [hcons I hI0] at happ
  rw [show
      (Ideal.ofList gs) • (⊤ : Submodule R (QuotSMulTop f M)) =
        Submodule.map π ((Ideal.ofList gs) • ⊤)
      by
      rw [hπ, Submodule.map_smul'']
      congr 1
      rw [Submodule.map_top, Submodule.range_mkQ]] at happ
  rw [Submodule.mem_map] at happ
  obtain ⟨z, hz, hzy⟩ := happ
  rw [hπ, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzy
  rw [ofList_cons_sup, Submodule.sup_smul]
  have hfspan : (f • (⊤ : Submodule R M)) = (Ideal.span {f}) • ⊤ :=
    (Submodule.ideal_span_singleton_smul f ⊤).symm
  have hyz : m I = z - (z - m I) := by abel
  rw [hyz]
  refine Submodule.sub_mem _ (Submodule.mem_sup_right hz) (Submodule.mem_sup_left ?_)
  rwa [← hfspan]

/-- A power of a `g`-regular element stays regular.
If `g` is a nonzerodivisor mod `J' M` (`hg`) then so is `g^l`: from
`g^l • x ∈ J'M` we conclude `x ∈ J'M`. Direct consequence of
`IsSMulRegular.pow` + `mem_of_isSMulRegular_quotient_of_smul_mem`. -/
theorem snoc_pow_regular_descend (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R)
    (hg : IsSMulRegular (M ⧸ (Ideal.ofList init • ⊤ : Submodule R M)) g) (l : ℕ) (x : M)
    (hx : (g ^ l) • x ∈ (Ideal.ofList init) • (⊤ : Submodule R M)) :
    x ∈ (Ideal.ofList init) • (⊤ : Submodule R M) :=
  mem_of_isSMulRegular_quotient_of_smul_mem (hg.pow l) hx

/-- `listPow init I'` lies in `(Ideal.ofList init) ^ (∑ i, I' i)`. -/
theorem listPow_mem_pow (init : List R) (I' : Fin init.length → ℕ) :
    listPow init I' ∈ (Ideal.ofList init) ^ (∑ i, I' i) := by
  unfold listPow
  have h1 : (∏ i, init[i] ^ I' i) ∈ ∏ i, (Ideal.ofList init) ^ (I' i) :=
    Ideal.prod_mem_prod fun i _ =>
      Ideal.pow_mem_pow (Ideal.subset_span (by exact List.getElem_mem _)) _
  rwa [Finset.prod_pow_eq_pow_sum] at h1

/-- `Ideal.ofList init` is the span of the (Fin-indexed) entries of `init`. -/
theorem ofList_eq_span_range (init : List R) :
    Ideal.ofList init = Ideal.span (Set.range (fun i : Fin init.length => init[i])) := by
  unfold Ideal.ofList
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hx
    obtain ⟨m, h, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨m, h⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.getElem_mem _

/-- Multiplying a monomial by a generator `init[j]` bumps the `j`-th
exponent by one. -/
theorem listPow_mul_gen (init : List R) (K' : Fin init.length → ℕ) (j : Fin init.length) :
    listPow init K' * init[j] = listPow init (Function.update K' j (K' j + 1)) := by
  unfold listPow
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  rw [←
    Finset.mul_prod_erase Finset.univ (fun i => init[i] ^ Function.update K' j (K' j + 1) i)
      (Finset.mem_univ j)]
  rw [Function.update_self]
  have he :
    (∏ x ∈ Finset.univ.erase j, init[x] ^ Function.update K' j (K' j + 1) x) =
      (∏ x ∈ Finset.univ.erase j, init[x] ^ K' x) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he, pow_succ]; ring

/-- Bumping one exponent of a tuple by one increases the total degree by one. -/
theorem sum_update_add_one (c : ℕ) (K' : Fin c → ℕ) (j : Fin c) :
    (∑ i, Function.update K' j (K' j + 1) i) = (∑ i, K' i) + 1 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  rw [← Finset.add_sum_erase Finset.univ K' (Finset.mem_univ j)]
  rw [Function.update_self]
  have he :
    (∑ x ∈ Finset.univ.erase j, Function.update K' j (K' j + 1) x) =
      (∑ x ∈ Finset.univ.erase j, K' x) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]; ring

/-- A bumped multi-index of total degree `k` has total degree `k+1`. -/
theorem update_mem_antidiag (c k : ℕ) (K' : Fin c → ℕ) (j : Fin c)
    (hK : K' ∈ Finset.Nat.antidiagonalTuple c k) :
    Function.update K' j (K' j + 1) ∈ Finset.Nat.antidiagonalTuple c (k + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hK ⊢
  rw [sum_update_add_one, hK]

/-- Every element of `(Ideal.ofList init)^k • N` is a combination
`∑_{|K'| = k} listPow init K' • v K'` of degree-`k` monomials with coefficients `v K' ∈ N`. -/
private theorem exists_listPow_repr_of_mem_smul (init : List R) (M : Type*) [AddCommGroup M]
    [Module R M] (N : Submodule R M) :
    ∀ (k : ℕ) (x : M),
      x ∈ (Ideal.ofList init) ^ k • N →
        ∃ v : (Fin init.length → ℕ) → M,
          (∀ K', v K' ∈ N) ∧
            x = ∑ K' ∈ Finset.Nat.antidiagonalTuple init.length k, listPow init K' • v K' := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, one_smul] at hx
    refine ⟨fun _ => x, ?_, ?_⟩
    · intro _; exact hx
    · rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
      change x = listPow init 0 • x
      rw [show listPow init 0 = 1 by
          unfold listPow; simp,
        one_smul]
  | succ k ih =>
    intro x hx
    rw [pow_succ', mul_smul] at hx
    refine Submodule.smul_induction_on' hx ?_ ?_
    · intro r hr y hy
      obtain ⟨v, hvmem, rfl⟩ := ih y hy
      rw [ofList_eq_span_range, Submodule.mem_span_range_iff_exists_fun] at hr
      obtain ⟨c, rfl⟩ := hr
      classical
      set S : Finset (Fin init.length × (Fin init.length → ℕ)) :=
        Finset.univ ×ˢ Finset.Nat.antidiagonalTuple init.length k with hS
      set gg : Fin init.length × (Fin init.length → ℕ) → (Fin init.length → ℕ) := fun p =>
        Function.update p.snd p.fst (p.snd p.fst + 1) with hgg
      refine ⟨fun L => ∑ p ∈ S.filter (fun p => gg p = L), c p.fst • v p.snd, ?_, ?_⟩
      · intro L
        apply Submodule.sum_mem
        intro p _
        exact Submodule.smul_mem _ _ (hvmem p.snd)
      · rw [Finset.sum_smul]
        have lhs_eq :
          (∑ i,
              (c i • init[i]) •
                ∑ K' ∈ Finset.Nat.antidiagonalTuple init.length k, listPow init K' • v K') =
            ∑ p ∈ S, (c p.fst • (listPow init (gg p) • v p.snd)) := by
          rw [hS, Finset.sum_product]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro K' _
          change
            (c i • init[i]) • (listPow init K' • v K') =
              c i • (listPow init (Function.update K' i (K' i + 1)) • v K')
          rw [smul_assoc]
          congr 1
          rw [smul_smul]
          rw [show init[i] * listPow init K' = listPow init (Function.update K' i (K' i + 1)) by
              rw [mul_comm]; exact listPow_mul_gen init K' i]
        rw [lhs_eq]
        rw [←
          Finset.sum_fiberwise_of_maps_to (t := Finset.Nat.antidiagonalTuple init.length (k + 1))
            (g := gg) (f := fun p => c p.fst • (listPow init (gg p) • v p.snd)) ?_]
        · refine Finset.sum_congr rfl fun L _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2, smul_comm]
        · intro p hp
          rw [hS, Finset.mem_product] at hp
          exact update_mem_antidiag _ _ _ _ hp.right
    · rintro x _ y _ ⟨wx, hwxm, hwx⟩ ⟨wy, hwym, hwy⟩
      refine ⟨fun L => wx L + wy L, ?_, ?_⟩
      · intro L; exact Submodule.add_mem _ (hwxm L) (hwym L)
      · rw [hwx, hwy, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro L _
        rw [smul_add]

/-- Every element of `(Ideal.ofList init)^k • ⊤` is a finite
combination `∑_{|K'| = k} listPow init K' • v K'` of degree-`k` monomials. -/
theorem exists_listPow_repr (init : List R) (M : Type*) [AddCommGroup M] [Module R M] :
    ∀ (k : ℕ) (x : M),
      x ∈ (Ideal.ofList init) ^ k • (⊤ : Submodule R M) →
        ∃ v : (Fin init.length → ℕ) → M,
          x = ∑ K' ∈ Finset.Nat.antidiagonalTuple init.length k, listPow init K' • v K' :=
  fun k x hx => (exists_listPow_repr_of_mem_smul init M ⊤ k x hx).imp fun _ h => h.2

/-- **Top-power extraction.** From an honest grouped relation
of length `l + 1`, the top coefficients `a l I'` (for `|I'| = n - l`) already lie in
`(Ideal.ofList init) • ⊤`. Uses `hinit` at degree `n - l` and the `g`-regularity
descent `snoc_pow_regular_descend`. -/
theorem snoc_top_level (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R)
    (hinit : IsQuasiregularSeq init M)
    (hg : IsSMulRegular (M ⧸ (Ideal.ofList init • ⊤ : Submodule R M)) g) (n l : ℕ) (hl : l ≤ n)
    (a : ℕ → (Fin init.length → ℕ) → M)
    (hrel :
      (∑ e ∈ Finset.range (l + 1),
          g ^ e •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e), listPow init I' • a e I')) =
        0) :
    ∀ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l),
      a l I' ∈ (Ideal.ofList init) • (⊤ : Submodule R M) := by
  rw [Finset.sum_range_succ] at hrel
  have htop_eq :
    (g ^ l • ∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l), listPow init I' • a l I') =
      -(∑ e ∈ Finset.range l,
          g ^ e •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
              listPow init I' • a e I')) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hrel
  have hlower :
    (∑ e ∈ Finset.range l,
        g ^ e •
          (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e), listPow init I' • a e I')) ∈
      (Ideal.ofList init) ^ (n - l + 1) • (⊤ : Submodule R M) := by
    apply Submodule.sum_mem
    intro e he
    rw [Finset.mem_range] at he
    rw [Finset.smul_sum]
    apply Submodule.sum_mem
    intro I' hI'
    rw [Finset.Nat.mem_antidiagonalTuple] at hI'
    rw [smul_comm]
    have hmem :
      listPow init I' • (g ^ e • a e I') ∈
        (Ideal.ofList init) ^ (n - e) • (⊤ : Submodule R M) := by
      have hh :
        listPow init I' • (g ^ e • a e I') ∈
          (Ideal.ofList init) ^ (n - e) • ((Ideal.ofList init) ^ 0 • (⊤ : Submodule R M)) := by
        apply Submodule.smul_mem_smul
        · rw [← hI']; exact listPow_mem_pow init I'
        · simp
      simpa using hh
    have hle :
      (Ideal.ofList init) ^ (n - e) • (⊤ : Submodule R M) ≤
        (Ideal.ofList init) ^ (n - l + 1) • ⊤ := by
      apply Submodule.smul_mono_left
      apply Ideal.pow_le_pow_right
      omega
    exact hle hmem
  have hAl :
    (g ^ l • ∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l), listPow init I' • a l I') ∈
      (Ideal.ofList init) ^ (n - l + 1) • (⊤ : Submodule R M) := by
    rw [htop_eq]; exact Submodule.neg_mem _ hlower
  have hrelform :
    (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l), listPow init I' • (g ^ l • a l I')) ∈
      (Ideal.ofList init) ^ ((n - l) + 1) • (⊤ : Submodule R M) := by
    have hcomm :
      (g ^ l • ∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l), listPow init I' • a l I') =
        ∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - l),
          listPow init I' • (g ^ l • a l I') := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro I' _; rw [smul_comm]
    rw [hcomm] at hAl; exact hAl
  have hgla := hinit (n - l) (fun I' => g ^ l • a l I') hrelform
  intro I' hI'
  exact snoc_pow_regular_descend M init g hg l (a l I') (hgla I' hI')

/-- **The analytic heart of the snoc step: the inner induction `C(l)`.**

Working with the prefix `init` (write `J' = (init)`, `J = (init ++ [g])`), the
`g`-exponent is carried as an explicit natural number `e` (NOT a `Fin`-tuple
coordinate), so the multi-index `I'` ranges over `Fin init.length → ℕ` only.

Statement: for every `l ≤ n` and every family `a : ℕ → (Fin init.length → ℕ) → M`,
if the *honest* (`= 0`) grouped relation
`∑_{e=0}^{l} g^e • (∑_{|I'| = n-e} listPow init I' • a e I') = 0`
holds, then `a e I' ∈ J M` for every `e ≤ l` and every `I'` with `|I'| = n-e`.

The proof is by induction on `l`.
* **Base `l = 0`.** The relation is `∑_{|I'|=n} listPow init I' • a 0 I' = 0 ∈ (J')^{n+1}M`,
  a degree-`n` quasi-regularity relation for `init`; `hinit` gives `a 0 I' ∈ J'M ⊆ JM`.
* **Step `l-1 ⇒ l`.** Isolate the top power:
  `g^l • (∑_{|I'|=n-l} listPow init I' • a l I') = -∑_{e<l} g^e • (…) ∈ (J')^{n-l+1}M`
  (each lower term has `|I'| = n-e ≥ n-l+1`, so `listPow init I' ∈ (J')^{n-l+1}`).
  This is a degree-`(n-l)` quasi-regularity relation for `init` with coefficients
  `g^l • a l I'`; `hinit` gives `g^l • a l I' ∈ J'M`, then `snoc_pow_regular_descend`
  (`hg`) gives `a l I' ∈ J'M ⊆ JM` (the top-level conclusion `e = l`).
  Then expand `a l I' = ∑_j (init[j]) • u …` and absorb `g^l•(top block)` into level
  `l-1` via `g^l = g·g^{l-1}`, defining a new family `a'` with
  `a' (l-1) I' = a (l-1) I' + g • v_{I'}` and `a' e = a e` for `e ≤ l-2`; the relation
  becomes the honest `(R_{l-1})` for `a'`. Apply the IH `C(l-1)` to get `a' e I' ∈ JM`
  for `e ≤ l-1`; read off `a e I' ∈ JM`: for `e ≤ l-2`, `a' = a`; for `e = l-1`,
  `a (l-1) I' = a' (l-1) I' - g•v_{I'}` with `a' (l-1) I' ∈ JM` and `g•v_{I'} ∈ gM ⊆ JM`
  (this is why the conclusion is stated as membership in `JM` rather than `J'M`: there
  the `gM` discrepancy is harmless). -/
theorem snoc_inner_induction (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R)
    (hinit : IsQuasiregularSeq init M)
    (hg : IsSMulRegular (M ⧸ (Ideal.ofList init • ⊤ : Submodule R M)) g) (n : ℕ) :
    ∀ l,
      l ≤ n →
        ∀ (a : ℕ → (Fin init.length → ℕ) → M),
          (∑ e ∈ Finset.range (l + 1),
                g ^ e •
                  (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                    listPow init I' • a e I')) =
              0 →
            ∀ e,
              e ≤ l →
                ∀ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                  a e I' ∈ (Ideal.ofList (init ++ [g])) • (⊤ : Submodule R M) := by
  have hJ'J : (Ideal.ofList init) • (⊤ : Submodule R M) ≤ (Ideal.ofList (init ++ [g])) • ⊤ :=
    Submodule.smul_mono_left (by rw [Ideal.ofList_append]; exact le_sup_left)
  have hgmem : ∀ m : M, g • m ∈ (Ideal.ofList (init ++ [g])) • (⊤ : Submodule R M) := by
    intro m
    refine Submodule.smul_mem_smul ?_ trivial
    apply Ideal.subset_span
    simp [List.mem_append]
  intro l
  induction l with
  | zero =>
    intro _ a hrel e he I' hI'
    obtain rfl : e = 0 := Nat.le_zero.mp he
    exact hJ'J (snoc_top_level M init g hinit hg n 0 (Nat.zero_le n) a hrel I' hI')
  | succ L ih =>
    intro hl a hrel
    have htop :
      ∀ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - (L + 1)),
        a (L + 1) I' ∈ (Ideal.ofList init) • (⊤ : Submodule R M) :=
      snoc_top_level M init g hinit hg n (L + 1) hl a hrel
    have hAtop :
      (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - (L + 1)),
          listPow init I' • a (L + 1) I') ∈
        (Ideal.ofList init) ^ ((n - (L + 1)) + 1) • (⊤ : Submodule R M) := by
      apply Submodule.sum_mem
      intro I' hI'
      rw [Finset.Nat.mem_antidiagonalTuple] at hI'
      have hh :
          listPow init I' • a (L + 1) I' ∈
            (Ideal.ofList init) ^ (n - (L + 1)) • ((Ideal.ofList init) • (⊤ : Submodule R M)) :=
        Submodule.smul_mem_smul (hI' ▸ listPow_mem_pow init I')
          (htop I' (Finset.Nat.mem_antidiagonalTuple.mpr hI'))
      rwa [← mul_smul, ← pow_succ] at hh
    obtain ⟨vrep, hvrep⟩ :=
      exists_listPow_repr init M ((n - (L + 1)) + 1)
        (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - (L + 1)),
          listPow init I' • a (L + 1) I')
        hAtop
    have hdeg : (n - (L + 1)) + 1 = n - L := by omega
    classical
    set a' : ℕ → (Fin init.length → ℕ) → M := fun e =>
      if e = L then (fun K' => a L K' + g • vrep K') else a e with ha'
    have ha'_L : a' L = (fun K' => a L K' + g • vrep K') := by
      rw [ha']
      simp
    have ha'_ne : ∀ e, e ≠ L → a' e = a e := by
      intro e he
      rw [ha']
      simp [he]
    have hrel' :
      (∑ e ∈ Finset.range (L + 1),
          g ^ e •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e), listPow init I' • a' e I')) =
        0 := by
      rw [Finset.sum_range_succ]
      have hlowereq :
        (∑ e ∈ Finset.range L,
            g ^ e •
              (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                listPow init I' • a' e I')) =
          (∑ e ∈ Finset.range L,
            g ^ e •
              (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                listPow init I' • a e I')) := by
        apply Finset.sum_congr rfl
        intro e he; rw [Finset.mem_range] at he
        rw [ha'_ne e (by omega)]
      have hLterm :
        g ^ L •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L), listPow init I' • a' L I') =
          g ^ L •
              (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L), listPow init I' • a L I') +
            g ^ (L + 1) •
              (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - (L + 1)),
                listPow init I' • a (L + 1) I') := by
        rw [ha'_L]
        have hsplit :
          (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L),
              listPow init I' • (a L I' + g • vrep I')) =
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L), listPow init I' • a L I') +
              g •
                (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L),
                  listPow init I' • vrep I') := by
          rw [Finset.smul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro I' _
          rw [smul_add]; congr 1; rw [smul_comm]
        rw [hsplit, smul_add]
        congr 1
        rw [hdeg] at hvrep
        rw [← hvrep, smul_smul, ← pow_succ]
      rw [hlowereq, hLterm, ← add_assoc]
      rw [show
          (∑ e ∈ Finset.range L,
                g ^ e •
                  (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                    listPow init I' • a e I')) +
              g ^ L •
                (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - L),
                  listPow init I' • a L I') =
            ∑ e ∈ Finset.range (L + 1),
              g ^ e •
                (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e), listPow init I' • a e I')
          from (Finset.sum_range_succ _ L).symm]
      rw [← Finset.sum_range_succ]
      exact hrel
    have hL_le : L ≤ n := by omega
    have hIH := ih hL_le a' hrel'
    intro e he I' hI'
    obtain hlt | rfl | rfl : e < L ∨ e = L ∨ e = L + 1 := by omega
    · rw [← ha'_ne e (by omega)]
      exact hIH e (by omega) I' hI'
    · have hmem := hIH _ le_rfl I' hI'
      rw [ha'_L] at hmem
      simpa only [add_sub_cancel_right] using Submodule.sub_mem _ hmem (hgmem (vrep I'))
    · exact hJ'J (htop I' hI')

/- Unfolds `IsQuasiregularSeq (init ++ [g]) M` to
the grouped, honest-`= 0` form fed to `snoc_inner_induction`.

Given the degree-`n` relation `∑_{I ∈ antidiagonalTuple (c+1) n} listPow (init++[g]) I • m I
∈ J^{n+1}M` (where `c = init.length`), produces a family
`a : ℕ → (Fin c → ℕ) → M` with `a e I' ≡ (the original coefficient at g-exponent e,
prefix index I') mod JM` such that the honest relation
`∑_{e=0}^n g^e • (∑_{|I'|=n-e} listPow init I' • a e I') = 0` holds, AND such that
`a e I' ∈ JM ↔ m (the corresponding full index) ∈ JM`.

This packages: (i) the last-coordinate peel `listPow (init++[g]) I = listPow init (I∘castSucc)
* g^(I last)` (`Fin.prod_univ_castSucc`); (ii) the last-coordinate reindexing of
`antidiagonalTuple (c+1) n` as `⨆_e {I' : |I'| = n-e}` (peel last coord); (iii) Step 1 of the
informal proof: subtract a representative `∑ f^I b_I` (`b_I ∈ JM`) of the `J^{n+1}M` element to
make the relation honest `= 0`, which only changes each `m I` by an element of `JM`. -/

/-- Every element of
`(Ideal.ofList init)^k • (Ideal.ofList init • ⊤)` is a finite combination
`∑_{|K'| = k} listPow init K' • v K'` of degree-`k` monomials whose coefficients
`v K'` all lie in `Ideal.ofList init • ⊤`. (The case `N = J • ⊤` of
`exists_listPow_repr_of_mem_smul`, keeping the membership `v K' ∈ J M` tracked.) -/
theorem exists_listPow_repr_JM (init : List R) (M : Type*) [AddCommGroup M] [Module R M] :
    ∀ (k : ℕ) (x : M),
      x ∈ (Ideal.ofList init) ^ k • ((Ideal.ofList init) • (⊤ : Submodule R M)) →
        ∃ v : (Fin init.length → ℕ) → M,
          (∀ K', v K' ∈ (Ideal.ofList init) • (⊤ : Submodule R M)) ∧
            x = ∑ K' ∈ Finset.Nat.antidiagonalTuple init.length k, listPow init K' • v K' :=
  exists_listPow_repr_of_mem_smul init M _


/-- Given a `g`-exponent `e` and a prefix
multi-index `I' : Fin init.length → ℕ`, produces the full multi-index for `init ++ [g]`
with last coordinate `e` and the remaining coordinates given by `I'`. -/
noncomputable def snocIdx (init : List R) (g : R) (e : ℕ) (I' : Fin init.length → ℕ) :
    Fin (init ++ [g]).length → ℕ := fun i =>
  (Fin.snoc I' e : Fin (init.length + 1) → ℕ)
    (Fin.cast (by simp : (init ++ [g]).length = init.length + 1) i)

/-- `listPow (init ++ [g]) (snocIdx init g e I') = listPow init I' * g ^ e`. -/
theorem listPow_snoc (init : List R) (g : R) (e : ℕ) (I' : Fin init.length → ℕ) :
    listPow (init ++ [g]) (snocIdx init g e I') = listPow init I' * g ^ e := by
  unfold listPow snocIdx
  rw [←
    Fin.prod_congr' (a := init.length + 1) (b := (init ++ [g]).length)
      (fun i =>
        (init ++ [g])[i] ^
          ((Fin.snoc I' e : Fin (init.length + 1) → ℕ)
            (Fin.cast (by simp : (init ++ [g]).length = init.length + 1) i)))
      (by simp)]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
    congr 1
    simp [List.getElem_append_left]
  · rw [Fin.snoc_last]
    congr 1
    simp

omit [CommRing R] in
/-- The last coordinate of `snocIdx init g e I'` is `e`. -/
theorem snocIdx_last (init : List R) (g : R) (e : ℕ) (I' : Fin init.length → ℕ) :
    snocIdx init g e I'
        (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.last init.length)) =
      e := by
  simp [snocIdx]

omit [CommRing R] in
/-- The `castSucc j` coordinate of `snocIdx init g e I'` is `I' j`. -/
theorem snocIdx_castSucc (init : List R) (g : R) (e : ℕ) (I' : Fin init.length → ℕ)
    (j : Fin init.length) :
    snocIdx init g e I'
        (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.castSucc j)) =
      I' j := by
  simp [snocIdx]

omit [CommRing R] in
/-- Reconstructing a full multi-index from its last coordinate and its prefix
gives back the original index. -/
theorem snocIdx_reconstruct (init : List R) (g : R) (a : Fin (init ++ [g]).length → ℕ) :
    snocIdx init g
        (a (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.last init.length)))
        (fun j =>
          a (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.castSucc j))) =
      a := by
  unfold snocIdx
  funext i
  set i' : Fin (init.length + 1) := Fin.cast (by simp) i with hi'
  rw [show i = Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) i' by simp [hi']]
  refine Fin.lastCases ?_ ?_ i'
  · simp
  · intro j; simp

omit [CommRing R] in
/-- The total degree of `snocIdx init g e I'` is `(∑ j, I' j) + e`. -/
theorem sum_snocIdx (init : List R) (g : R) (e : ℕ) (I' : Fin init.length → ℕ) :
    (∑ i, snocIdx init g e I' i) = (∑ j, I' j) + e := by
  unfold snocIdx
  rw [←
    Fin.sum_congr' (a := init.length + 1) (b := (init ++ [g]).length)
      (fun i =>
        (Fin.snoc I' e : Fin (init.length + 1) → ℕ)
          (Fin.cast (by simp : (init ++ [g]).length = init.length + 1) i))
      (by simp)]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl; intro j _; rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

omit [CommRing R] in
/-- Splitting the total degree of a full index into prefix part and last
coordinate. -/
theorem sum_split (init : List R) (g : R) (a : Fin (init ++ [g]).length → ℕ) :
    (∑ i, a i) =
      (∑ j : Fin init.length,
          a (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.castSucc j))) +
        a
          (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length)
            (Fin.last init.length)) := by
  rw [← Fin.sum_congr' (a := init.length + 1) (b := (init ++ [g]).length) a (by simp)]
  rw [Fin.sum_univ_castSucc]

/-- Rewrites a degree-`n` single sum over the
full index set `antidiagonalTuple (init ++ [g]).length n` as the grouped double sum over
the `g`-exponent `e` and the prefix index `I'`, using `listPow_snoc` and the last-coordinate
bijection `(e, I') ↦ snocIdx init g e I'`. -/
theorem reindex_eq (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R) (n : ℕ)
    (mc : (Fin (init ++ [g]).length → ℕ) → M) :
    (∑ K ∈ Finset.Nat.antidiagonalTuple (init ++ [g]).length n, listPow (init ++ [g]) K • mc K) =
      ∑ e ∈ Finset.range (n + 1),
        g ^ e •
          (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
            listPow init I' • mc (snocIdx init g e I')) := by
  have hRHS :
    (∑ e ∈ Finset.range (n + 1),
        g ^ e •
          (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
            listPow init I' • mc (snocIdx init g e I'))) =
      ∑ e ∈ Finset.range (n + 1),
        (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
          listPow (init ++ [g]) (snocIdx init g e I') • mc (snocIdx init g e I')) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro I' _
    rw [listPow_snoc, mul_comm, ← smul_smul, smul_comm]
  rw [hRHS]
  rw [Finset.sum_sigma' (Finset.range (n + 1))
      (fun e => Finset.Nat.antidiagonalTuple init.length (n - e))
      (fun e I' => listPow (init ++ [g]) (snocIdx init g e I') • mc (snocIdx init g e I'))]
  apply
    Finset.sum_nbij' (i := fun K =>
      (⟨K (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.last init.length)),
          fun j =>
          K (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.castSucc j))⟩ :
        (_ : ℕ) × (Fin init.length → ℕ)))
      (j := fun p => snocIdx init g p.fst p.snd)
  · intro K hK
    rw [Finset.Nat.mem_antidiagonalTuple] at hK
    rw [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
    rw [sum_split] at hK
    dsimp only
    omega
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hp
    rw [Finset.Nat.mem_antidiagonalTuple, sum_snocIdx]
    omega
  · intro K _
    exact snocIdx_reconstruct init g K
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_range] at hp
    refine Sigma.ext ?_ ?_
    · simp [snocIdx_last]
    · exact heq_of_eq (funext fun j => snocIdx_castSucc init g p.fst p.snd j)
  · intro K _
    rw [snocIdx_reconstruct init g K]

/-- Bridge to the grouped form of a degree-`n` relation for `init ++ [g]`: after
subtracting a representative of the `J^{n+1}M` term the relation becomes honest
(`= 0`), and regrouping by the exponent of `g` presents it as a family
`a : ℕ → (Fin init.length → ℕ) → M` with `∑_e g^e • (∑_{|I'| = n-e} init^{I'} • a e I')
= 0`. If every `a e I'` lies in `J M`, so does the original coefficient `m I`. -/
theorem snoc_reduce_to_grouped (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R)
    (n : ℕ) (m : (Fin (init ++ [g]).length → ℕ) → M)
    (hsum :
      (∑ I ∈ Finset.Nat.antidiagonalTuple (init ++ [g]).length n, listPow (init ++ [g]) I • m I) ∈
        (Ideal.ofList (init ++ [g]) ^ (n + 1)) • (⊤ : Submodule R M))
    (I : (Fin (init ++ [g]).length → ℕ))
    (hI : I ∈ Finset.Nat.antidiagonalTuple (init ++ [g]).length n) :
    ∃ a : ℕ → (Fin init.length → ℕ) → M,
      (∑ e ∈ Finset.range (n + 1),
            g ^ e •
              (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                listPow init I' • a e I')) =
          0 ∧
        ((∀ e,
            e ≤ n →
              ∀ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
                a e I' ∈ (Ideal.ofList (init ++ [g])) • (⊤ : Submodule R M)) →
          m I ∈ (Ideal.ofList (init ++ [g])) • (⊤ : Submodule R M)) := by
  -- Step 1: subtract a `JM`-coefficient representative of the `J^{n+1}M` element to make the
  -- relation honest (`= 0`); each coefficient is only changed by an element of `JM`.
  rw [pow_succ, mul_smul] at hsum
  obtain ⟨c, hcmem, hceq⟩ := exists_listPow_repr_JM (init ++ [g]) M n _ hsum
  obtain ⟨mc, hmcdef⟩ : ∃ mc : (Fin (init ++ [g]).length → ℕ) → M, ∀ K, mc K = m K - c K :=
    ⟨fun K => m K - c K, fun _ => rfl⟩
  have hmc0 :
    (∑ K ∈ Finset.Nat.antidiagonalTuple (init ++ [g]).length n, listPow (init ++ [g]) K • mc K) =
      0 := by
    simp only [hmcdef, smul_sub, Finset.sum_sub_distrib]
    rw [← hceq, sub_self]
  obtain ⟨a, hadef⟩ :
    ∃ a : ℕ → (Fin init.length → ℕ) → M, ∀ e I', a e I' = mc (snocIdx init g e I') :=
    ⟨fun e I' => mc (snocIdx init g e I'), fun _ _ => rfl⟩
  refine ⟨a, ?_, ?_⟩
  · -- Conjunct 1: the grouped relation equals the honest single-sum relation, hence `= 0`.
    have hcongr :
      (∑ e ∈ Finset.range (n + 1),
          g ^ e •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e), listPow init I' • a e I')) =
        ∑ e ∈ Finset.range (n + 1),
          g ^ e •
            (∑ I' ∈ Finset.Nat.antidiagonalTuple init.length (n - e),
              listPow init I' • mc (snocIdx init g e I')) := by
      apply Finset.sum_congr rfl; intro e _; congr 1
      apply Finset.sum_congr rfl; intro I' _; rw [hadef]
    rw [hcongr, ← reindex_eq]
    exact hmc0
  · -- Conjunct 2: read off membership at the specific index `I`.
    intro hyp
    have hsumI : ∑ i, I i = n := Finset.Nat.mem_antidiagonalTuple.mp hI
    rw [sum_split] at hsumI
    have he₀n :
      I (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.last init.length)) ≤
        n := by
      omega
    have hI'₀mem :
      (fun j => I (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length) (Fin.castSucc j))) ∈
        Finset.Nat.antidiagonalTuple init.length
          (n -
            I
              (Fin.cast (by simp : init.length + 1 = (init ++ [g]).length)
                (Fin.last init.length))) := by
      rw [Finset.Nat.mem_antidiagonalTuple]; omega
    have hkey := hyp _ he₀n _ hI'₀mem
    rw [hadef] at hkey
    rw [snocIdx_reconstruct init g I] at hkey
    have hmI : m I = mc I + c I := by
      rw [hmcdef]; abel
    rw [hmI]
    exact Submodule.add_mem _ hkey (hcmem I)

/-- The snoc step: if `init` is `M`-quasi-regular and `g` is a nonzerodivisor on
`M / (init) M`, then `init ++ [g]` is `M`-quasi-regular. -/
theorem isQuasiregularSeq_snoc (M : Type*) [AddCommGroup M] [Module R M] (init : List R) (g : R)
    (hinit : IsQuasiregularSeq init M)
    (hg : IsSMulRegular (M ⧸ (Ideal.ofList init • ⊤ : Submodule R M)) g) :
    IsQuasiregularSeq (init ++ [g]) M := by
  intro n m hsum I hI
  -- Step 1 + bridge: obtain the honest grouped family `a` and the read-off implication.
  obtain ⟨a, hrel, hread⟩ := snoc_reduce_to_grouped M init g n m hsum I hI
  -- Apply the inner induction `C(n)` to the honest relation to get all `a e I' ∈ JM`.
  exact
    hread (fun e he I' hI' => snoc_inner_induction M init g hinit hg n n le_rfl a hrel e he I' hI')

/-- **Statement 2.** An `M`-regular sequence (Mathlib's `IsRegular`, i.e. the
full Definition 1 including `M/JM ≠ 0`) is `M`-quasi-regular.

Proved by REVERSE induction (last-element peel) on `rs` via `List.reverseRecOn`,
using `isQuasiregularSeq_snoc` for the step. -/
@[stacks 00LN "(2)", ega "0 15.1.10" "necessity", ega "0 15.1.9" "first assertion", ega "IV 19.5.1"
  "a) ⇒ c)"]
theorem isRegular_isQuasiregularSeq (M : Type*) [AddCommGroup M] [Module R M] (rs : List R)
    (h : RingTheory.Sequence.IsRegular M rs) : IsQuasiregularSeq rs M := by
  -- The condition `M/JM ≠ 0` is not needed; reduce to weak regularity.
  have hw : IsWeaklyRegular M rs := h.toIsWeaklyRegular
  clear h
  -- Reverse (last-element) induction on the list.
  induction rs using List.reverseRecOn with
  | nil => exact isQuasiregularSeq_nil M
  | append_singleton init g ih =>
    -- Split weak regularity of `init ++ [g]` into the prefix and the last element.
    rw [isWeaklyRegular_append_iff] at hw
    obtain ⟨hinit_wr, hg_wr⟩ := hw
    -- `hinit` from the inductive hypothesis applied to `init`.
    have hinit : IsQuasiregularSeq init M := ih hinit_wr
    -- `hg` : `g` nonzerodivisor mod `(init) M`, from the singleton factor.
    rw [isWeaklyRegular_singleton_iff] at hg_wr
    exact isQuasiregularSeq_snoc M init g hinit hg_wr

/-- **Statement 1.** A regular sequence of `R` (the case `M = R`) is a
quasi-regular sequence. This is the special case `M = R` of Statement 2. -/
@[stacks 00LN "(1)", ega "0 15.1.9" "first part, M = R", ega "IV 19.5.1" "a) ⇒ c) for M = A"]
theorem isRegular_isQuasiregularSeq_self (rs : List R) (h : RingTheory.Sequence.IsRegular R rs) :
    IsQuasiregularSeq rs R :=
  isRegular_isQuasiregularSeq R rs h

end Stacks.QuasiregularSequence
