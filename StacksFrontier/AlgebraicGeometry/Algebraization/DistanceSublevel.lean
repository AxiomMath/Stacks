module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.Topology.Dimension.CatenaryAdditive

/-!
# Specialization stability of the distance sublevel sets

For a closed subset `Z` of a Noetherian scheme `Y`, every sublevel set of the distance
from `Z` is stable under specialization.

## Main results

* `Stacks.Algebraization.distanceFunction_sublevel_stableUnderSpecialization`
  states specialization stability of the distance sublevel sets.

## Implementation notes

The distance takes values in `ℕ∞`, so the threshold is allowed to be any element of
`ℕ∞`; the infinite sublevel set is all of `Y`. A system ending at `y'` is carried to one
ending at a specialization `y` of `y'` in one of two ways: if its last ascending leg is
trivial, the last pair of endpoints is replaced by the closure of `y`, and otherwise a new
trivial leg at the closure of `y` is appended. Neither operation increases the weight.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- The closure of a specialization is contained in the closure of the point. -/
private lemma closureSingleton_le_of_mem_closure {Y : Scheme.{u}} {y y' : Y}
    (hspec : y ∈ closure ({y'} : Set Y)) :
    IrreducibleCloseds.closureSingleton y ≤ IrreducibleCloseds.closureSingleton y' :=
  (specializes_iff_mem_closure.mpr hspec).closure_subset

/-- If the last ascending leg of `s` is trivial, the closure of a specialization `y` of the
endpoint lies in its last lower endpoint. -/
private lemma closureSingleton_le_V_last
    {Y : Scheme.{u}} [IsNoetherian Y] {Z : Closeds Y} {y y' : Y}
    (s : DistanceSystem Y Z y') (hspec : y ∈ closure ({y'} : Set Y))
    (hfinal : s.V (Fin.last s.k) = s.W (Fin.last s.k)) :
    IrreducibleCloseds.closureSingleton y ≤ s.V (Fin.last s.k) := by
  rw [hfinal, s.W_last_eq_closureSingleton]
  exact closureSingleton_le_of_mem_closure hspec

/-- Replace the last pair of endpoints of a system ending at `y'` by the closure of a
specialization `y` of `y'`, when the last ascending leg is trivial. -/
private abbrev replaceTerminal
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) {y y' : Y}
    (s : DistanceSystem Y Z y')
    (hspec : y ∈ closure ({y'} : Set Y))
    (hfinal : s.V (Fin.last s.k) = s.W (Fin.last s.k)) :
    DistanceSystem Y Z y where
  k := s.k
  V := fun i => if i = Fin.last s.k then IrreducibleCloseds.closureSingleton y else s.V i
  W := fun i => if i = Fin.last s.k then IrreducibleCloseds.closureSingleton y else s.W i
  V_le_W := by
    intro i
    by_cases hi : i = Fin.last s.k
    · simp [hi]
    · simpa [hi] using s.V_le_W i
  V_next_le_W := by
    intro i
    by_cases hi : Fin.succ i = Fin.last s.k
    · rw [hi]
      have hA := closureSingleton_le_V_last s hspec hfinal
      have h := s.V_next_le_W i
      rw [hi] at h
      have hcast : i.castSucc ≠ Fin.last s.k := (Fin.castSucc_lt_last i).ne
      simpa [hi, hcast] using hA.trans h
    · simpa [hi] using s.V_next_le_W i
  V_zero_subset := by
    by_cases hzero : (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) = Fin.last s.k
    · simp only [ite_eq_left hzero]
      have hA : (IrreducibleCloseds.closureSingleton y : Set Y) ⊆
          (s.V (Fin.last s.k) : Set Y) := closureSingleton_le_V_last s hspec hfinal
      have hs0 := s.V_zero_subset
      change (s.V (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) : Set Y) ⊆ (Z : Set Y) at hs0
      rw [hzero] at hs0
      exact hA.trans hs0
    · simpa only [ite_eq_right hzero] using s.V_zero_subset
  W_last_eq_closure := by simp

/-- Append a trivial leg at the closure of a specialization `y` of `y'` to a system
ending at `y'`. -/
private abbrev appendTerminal
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) {y y' : Y}
    (s : DistanceSystem Y Z y')
    (hspec : y ∈ closure ({y'} : Set Y)) :
    DistanceSystem Y Z y where
  k := s.k + 1
  V := Fin.snoc s.V (IrreducibleCloseds.closureSingleton y)
  W := Fin.snoc s.W (IrreducibleCloseds.closureSingleton y)
  V_le_W := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa [Fin.snoc_castSucc] using s.V_le_W j
  V_next_le_W := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
      rw [s.W_last_eq_closureSingleton]
      exact closureSingleton_le_of_mem_closure hspec
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using s.V_next_le_W j
  V_zero_subset := by
    simpa [Fin.snoc_castSucc] using s.V_zero_subset
  W_last_eq_closure := by simp

/-- Replacing the last pair of endpoints does not increase the weight: the last ascending
leg stays trivial and the last descending leg can only grow. -/
private lemma replaceTerminal_weight_le
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) {y y' : Y}
    (s : DistanceSystem Y Z y')
    (hspec : y ∈ closure ({y'} : Set Y))
    (hfinal : s.V (Fin.last s.k) = s.W (Fin.last s.k)) :
    (replaceTerminal Y Z s hspec hfinal).weight ≤ s.weight := by
  classical
  have hup (i : Fin (s.k + 1)) :
      (replaceTerminal Y Z s hspec hfinal).upCodimension i = s.upCodimension i := by
    by_cases hi : i = Fin.last s.k
    · subst i
      simp [DistanceSystem.upCodimension, hfinal, topCodim_self_eq_zero]
    · simp [DistanceSystem.upCodimension, hi]
  have hdown (i : Fin s.k) :
      s.downCodimension i ≤ (replaceTerminal Y Z s hspec hfinal).downCodimension i := by
    by_cases hi : i.succ = Fin.last s.k
    · have hcast : i.castSucc ≠ Fin.last s.k := (Fin.castSucc_lt_last i).ne
      have hW : (replaceTerminal Y Z s hspec hfinal).W i.castSucc = s.W i.castSucc := by
        simp [hcast]
      have hV : (replaceTerminal Y Z s hspec hfinal).V (Fin.last s.k) ≤
          s.V (Fin.last s.k) := by
        have hVlast : (replaceTerminal Y Z s hspec hfinal).V (Fin.last s.k) =
            IrreducibleCloseds.closureSingleton y := by
          simp
        rw [hVlast]
        exact closureSingleton_le_V_last s hspec hfinal
      unfold DistanceSystem.downCodimension
      dsimp at hV hW ⊢
      rw [hi, hW]
      exact topCodim_toNat_anti_left Y hV
    · simp [DistanceSystem.downCodimension, hi]
  unfold DistanceSystem.weight
  apply Nat.add_le_add_left
  apply Finset.sup_le
  intro i hi
  have hu :
      (∑ j : Fin (s.k + 1), if i.val ≤ j.val then
          (replaceTerminal Y Z s hspec hfinal).upCodimension j else 0) =
        ∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0 :=
    Finset.sum_congr rfl fun j _ => by rw [hup j]
  have hd :
      (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0) ≤
        ∑ j : Fin s.k, if i.val ≤ j.val then
          (replaceTerminal Y Z s hspec hfinal).downCodimension j else 0 :=
    Finset.sum_le_sum fun j _ => by split_ifs; exacts [hdown j, le_rfl]
  rw [hu]
  refine (Nat.sub_le_sub_left hd _).trans ?_
  exact Finset.le_sup
    (f := fun j : Fin (s.k + 1) =>
      (∑ l : Fin (s.k + 1), if j.val ≤ l.val then s.upCodimension l else 0) -
      (∑ l : Fin s.k, if j.val ≤ l.val then s.downCodimension l else 0))
    (Finset.mem_univ i)

/-- Appending a trivial leg does not increase the weight: the extra leg costs one in the
leading `k`, and the new strict descending leg saves at least one in the maximum. -/
private lemma appendTerminal_weight_le
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) {y y' : Y}
    (s : DistanceSystem Y Z y')
    (hspec : y ∈ closure ({y'} : Set Y))
    (hne : y ≠ y')
    (hneq : s.V (Fin.last s.k) ≠ s.W (Fin.last s.k)) :
    (appendTerminal Y Z s hspec).weight ≤ s.weight := by
  classical
  have hup_cast (i : Fin (s.k + 1)) :
      (appendTerminal Y Z s hspec).upCodimension i.castSucc = s.upCodimension i := by
    simp [DistanceSystem.upCodimension]
  have hup_last : (appendTerminal Y Z s hspec).upCodimension (Fin.last (s.k + 1)) = 0 := by
    simp [DistanceSystem.upCodimension, topCodim_self_eq_zero]
  have hdown_cast (i : Fin s.k) :
      (appendTerminal Y Z s hspec).downCodimension i.castSucc = s.downCodimension i := by
    unfold DistanceSystem.downCodimension
    simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
  have hterm {x : Y} (t : DistanceSystem Y Z x) :
      (∑ j : Fin (t.k + 1), if (Fin.last t.k).val ≤ j.val then t.upCodimension j else 0) -
        (∑ j : Fin t.k, if (Fin.last t.k).val ≤ j.val then t.downCodimension j else 0) =
        t.upCodimension (Fin.last t.k) := by
    have hd :
        (∑ j : Fin t.k, if (Fin.last t.k).val ≤ j.val then t.downCodimension j else 0) = 0 := by
      simp [Fin.val_last]
    rw [hd, Nat.sub_zero, Fin.sum_univ_castSucc]
    simp [Fin.val_castSucc, Fin.val_last]
  have hstrict : IrreducibleCloseds.closureSingleton y <
      IrreducibleCloseds.closureSingleton y' := by
    refine lt_of_le_of_ne (closureSingleton_le_of_mem_closure hspec) fun heq => hne ?_
    have hsets : closure ({y} : Set Y) = closure ({y'} : Set Y) := by
      simpa using congrArg (fun V : IrreducibleCloseds Y => (V : Set Y)) heq
    have hrev : y' ∈ closure ({y} : Set Y) := by
      rw [hsets]
      exact subset_closure (by simp)
    exact ((specializes_iff_mem_closure.mpr hspec).antisymm
      (specializes_iff_mem_closure.mpr hrev)).eq.symm
  have hnewdown : 0 < (appendTerminal Y Z s hspec).downCodimension (Fin.last s.k) := by
    apply topCodim_toNat_pos_of_lt Y
    simpa [Fin.snoc_last, Fin.snoc_castSucc, s.W_last_eq_closureSingleton] using hstrict
  unfold DistanceSystem.weight
  let M := (Finset.univ : Finset (Fin (s.k + 1))).sup (fun i =>
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
    (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))
  let N := (Finset.univ : Finset (Fin (s.k + 2))).sup (fun i =>
    (∑ j : Fin (s.k + 2), if i.val ≤ j.val then
      (appendTerminal Y Z s hspec).upCodimension j else 0) -
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then
      (appendTerminal Y Z s hspec).downCodimension j else 0))
  have hM : 1 ≤ M := by
    have hpos := s.upCodimension_pos_of_lt (Fin.last s.k) ((s.V_le_W _).lt_of_ne hneq)
    have hs := Finset.le_sup
      (f := fun i : Fin (s.k + 1) =>
        (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
        (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))
      (Finset.mem_univ (Fin.last s.k))
    rw [hterm s] at hs
    omega
  have hNM : N ≤ M - 1 := by
    dsimp [N, M]
    apply Finset.sup_le
    intro i hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ((hterm (appendTerminal Y Z s hspec)).trans hup_last).le.trans (Nat.zero_le _)
    · have hU :
          (∑ l : Fin (s.k + 2), if j.castSucc.val ≤ l.val then
            (appendTerminal Y Z s hspec).upCodimension l else 0) =
          ∑ l : Fin (s.k + 1), if j.val ≤ l.val then s.upCodimension l else 0 := by
        rw [Fin.sum_univ_castSucc]
        simp [Fin.val_castSucc, Fin.val_last, hup_cast, hup_last]
      have hD :
          (∑ l : Fin (s.k + 1), if j.castSucc.val ≤ l.val then
            (appendTerminal Y Z s hspec).downCodimension l else 0) =
          (∑ l : Fin s.k, if j.val ≤ l.val then s.downCodimension l else 0) +
            (appendTerminal Y Z s hspec).downCodimension (Fin.last s.k) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, hdown_cast]
        have hj : j.val ≤ s.k := Nat.le_of_lt_succ j.isLt
        simp [hj]
      rw [hU, hD]
      have hs := Finset.le_sup
        (f := fun i : Fin (s.k + 1) =>
          (∑ l : Fin (s.k + 1), if i.val ≤ l.val then s.upCodimension l else 0) -
          (∑ l : Fin s.k, if i.val ≤ l.val then s.downCodimension l else 0))
        (Finset.mem_univ j)
      omega
  change s.k + 1 + N ≤ s.k + M
  omega

/-- **Stacks Project, Tag 0EIY.** Sublevel sets of the distance from a closed subset of a
Noetherian scheme are stable under specialization. -/
@[stacks 0EIY "sublevel_specialization_stable"]
public theorem distanceFunction_sublevel_stableUnderSpecialization
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (k : ℕ∞) :
    StableUnderSpecialization {y : Y | distanceFunction Y Z y ≤ k} := by
  classical
  intro y' y hspecializes hy'
  have hspec : y ∈ closure ({y'} : Set Y) := hspecializes.mem_closure
  simp only [Set.mem_ofPred_eq] at hy' ⊢
  by_cases hk : k = ⊤
  · simp [hk]
  have hmeet' : (connectedComponent y' ∩ (Z : Set Y)).Nonempty := by
    by_contra hdis
    have htop := distanceFunction_eq_top_of_disjoint Y Z y' hdis
    rw [htop] at hy'
    simp [hk] at hy'
  have hcc : connectedComponent y' = connectedComponent y :=
    connectedComponent_eq (closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent hspec)
  have hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty := by
    simpa only [← hcc] using hmeet'
  by_cases heq : y = y'
  · subst y
    exact hy'
  have := nonempty_distanceSystem_of_connectedComponent_inter Y Z y' hmeet'
  obtain ⟨s, hsmin⟩ := ENat.exists_eq_iInf (fun s : DistanceSystem Y Z y' => (s.weight : ℕ∞))
  have hsbound : (s.weight : ℕ∞) ≤ k :=
    (hsmin.trans (distanceFunction_eq_iInf_of_nonempty Y Z y' hmeet').symm).trans_le hy'
  have hsystem : ∃ t : DistanceSystem Y Z y, t.weight ≤ s.weight := by
    by_cases hfinal : s.V (Fin.last s.k) = s.W (Fin.last s.k)
    · exact ⟨replaceTerminal Y Z s hspec hfinal,
        replaceTerminal_weight_le Y Z s hspec hfinal⟩
    · exact ⟨appendTerminal Y Z s hspec,
        appendTerminal_weight_le Y Z s hspec heq hfinal⟩
  obtain ⟨t, ht⟩ := hsystem
  rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet]
  have ht' : (t.weight : ℕ∞) ≤ (s.weight : ℕ∞) := by exact_mod_cast ht
  exact (iInf_le (fun q : DistanceSystem Y Z y => (q.weight : ℕ∞)) t).trans
    (ht'.trans hsbound)

end Stacks.Algebraization
