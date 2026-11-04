module

public import Mathlib.GroupTheory.Index

/-! # Index of a subgroup -/

@[expose] public section

open Subgroup

/-- For subgroups `S₁ ≤ S₂` of `G` with `S₂` of finite index, the index of `S₁` inside `S₂`
equals `[G : S₁] / [G : S₂]`. -/
@[simp] theorem Subgroup.index_subgroupOf {G : Type*} [Group G] {S₁ S₂ : Subgroup G}
    [S₂.FiniteIndex] (hS : S₁ ≤ S₂) : (S₁.subgroupOf S₂).index = S₁.index / S₂.index := by
  simp_rw [index, Nat.card_congr (quotientEquivProdOfLE hS), Nat.card_prod, ← index.eq_1,
    Nat.mul_div_cancel_left _ <| Nat.pos_of_ne_zero <| FiniteIndex.index_ne_zero (H := S₂)]

/-- If `S₁ ≤ S₂` are subgroups of `G` with `S₁` of finite index and `[G : S₁] ≤ [G : S₂]`,
then `S₁ = S₂`. -/
theorem Subgroup.eq_of_le_of_index_le {G : Type*} [Group G] {S₁ S₂ : Subgroup G}
    [S₁.FiniteIndex] (hS : S₁ ≤ S₂) (hSi : S₁.index ≤ S₂.index) : S₁ = S₂ := by
  refine le_antisymm hS ?_
  have := finiteIndex_of_le hS
  replace hSi := le_antisymm hSi <| index_antitone hS
  rw [← subgroupOf_eq_top, ← index_eq_one, index_subgroupOf hS, hSi,
    Nat.div_self <| Nat.pos_of_ne_zero <| FiniteIndex.index_ne_zero (H := S₂)]
