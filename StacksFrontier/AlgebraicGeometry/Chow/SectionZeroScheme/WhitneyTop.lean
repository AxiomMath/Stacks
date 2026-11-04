module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum

/-!
# The top Chern class of an extension by an invertible quotient

For a short exact sequence `0 ⟶ ℰ' ⟶ ℰ ⟶ ℒ ⟶ 0` of finite locally free modules of ranks
`m`, `m + 1` and `1`, the Whitney sum formula [Stacks, Tag 02UI] gives in top degree

  `c_{m + 1}(ℰ) ∩ α = c_m(ℰ') ∩ c_1(ℒ) ∩ α`,

since `c_j(ℰ') = 0` for `j > m` and `c_j(ℒ) = 0` for `j > 1`. This is the first equality of the
display in the proof of [Stacks, Tag 0FA9].

## Main results

* `Stacks.Chow.SectionZeroScheme.chernCap_top_eq_of_shortExact`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.SectionZeroScheme

open Stacks.Chow.GenuineChern

/-- For `i ≤ s`, the degree `i` term of the Chern family of a finite locally free module of rank
`s` is the cap product with its `i`-th Chern class. -/
theorem chernFamily_of_le' (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] (k : ℤ) {i : ℕ}
    (h : i ≤ s) : chernFamily C q M s k i = chernCap C s q M k ⟨i, Nat.lt_succ_of_le h⟩ :=
  chernCapFamilyOnChow_of_le C (chernCap C) q M s k h

/-- For `i > s`, the degree `i` term of the Chern family of a finite locally free module of rank
`s` vanishes. -/
theorem chernFamily_of_gt' (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] (k : ℤ) {i : ℕ}
    (h : ¬ i ≤ s) : chernFamily C q M s k i = 0 :=
  chernCapFamilyOnChow_of_gt C (chernCap C) q M s k h

/-- The Chern class cap products, applied at equal degrees, indices and arguments. -/
theorem chernCap_heq_congr (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] {k k' : ℤ}
    (hk : k = k') {i i' : Fin (s + 1)} (hi : i = i') {β : chowGroup C q k}
    {β' : chowGroup C q k'} (hβ : β ≍ β') :
    chernCap C s q M k i β ≍ chernCap C s q M k' i' β' := by
  subst hk
  subst hi
  cases hβ
  rfl

/-- **The top Chern class of an extension by an invertible quotient**:
`c_{m + 1}(ℰ) ∩ α = c_m(ℰ') ∩ c_1(ℒ) ∩ α`, up to the identification of the degrees. -/
theorem chernCap_top_eq_of_shortExact (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (S : ShortComplex T.Modules) (hS : S.ShortExact) (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ m]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (m + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ 1]
    (k : ℤ) (α : chowGroup C q k) :
    chernCap C (m + 1) q S.X₂ k (Fin.last (m + 1)) α ≍
      chernCap C m q S.X₁ (k - 1) (Fin.last m) (chernCap C 1 q S.X₃ k (Fin.last 1) α) := by
  have hW := chernFamily_eq_mul_of_shortExact C q S hS m 1
  have h := congrArg (fun F : GradedCapFamily (chowGroup C q) => F k (m + 1) α) hW
  rw [gradedCap_mul_def, convolve_apply] at h
  rw [DFunLike.congr_fun (chernFamily_of_le' C q S.X₂ (m + 1) k le_rfl) α] at h
  refine (heq_of_eq h).trans ?_
  rw [Finset.sum_eq_single 1]
  · rw [convolveTerm_of_le _ _ k (by omega : 1 ≤ m + 1), capTo_def]
    refine (gradedDegreeCast_heq _ _).trans ?_
    refine (heq_of_eq (DFunLike.congr_fun
      (chernFamily_of_le' C q S.X₁ m (k - ((1 : ℕ) : ℤ)) (by omega : m + 1 - 1 ≤ m)) _)).trans ?_
    refine chernCap_heq_congr C q S.X₁ m (by simp) (Fin.ext (by simp)) ?_
    exact heq_of_eq (DFunLike.congr_fun (chernFamily_of_le' C q S.X₃ 1 k le_rfl) α)
  · intro j _ hj
    rcases Nat.lt_or_gt_of_ne hj with hj0 | hj2
    · obtain rfl : j = 0 := by omega
      rw [convolveTerm_of_le _ _ k (Nat.zero_le _), capTo_def,
        chernFamily_of_gt' C q S.X₁ m _ (by omega : ¬ m + 1 - 0 ≤ m), AddMonoidHom.zero_apply,
        map_zero]
    · by_cases hjm : j ≤ m + 1
      · rw [convolveTerm_of_le _ _ k hjm, capTo_def,
          chernFamily_of_gt' C q S.X₃ 1 k (by omega : ¬ j ≤ 1),
          AddMonoidHom.zero_apply, map_zero, map_zero]
      · rw [convolveTerm, dite_eq_right hjm, AddMonoidHom.zero_apply]
  · intro h1
    exact absurd (Finset.mem_range.2 (by omega)) h1

end Stacks.Chow.SectionZeroScheme

end
