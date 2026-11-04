module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Cyclic groups -/

@[expose] public section

open Finset

@[to_additive (attr := stacks 09HX)]
theorem isCyclic_of_card_pow_eq_one_le_of_dvd
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hpow : ∀ x : G, x ^ n = 1)
    (hcard : ∀ d, d ∣ n → {x : G | x ^ d = 1}.ncard ≤ d) : IsCyclic G :=
  have := Fintype.ofFinite G
  have := Classical.decEq G
  isCyclic_of_card_pow_eq_one_le fun d hd ↦ calc
  #{x : G | x ^ d = 1}
    ≤ #{x : G | x ^ d.gcd n = 1} := card_le_card fun x ↦ by simp [hpow]
  _ ≤ d.gcd n := by simpa [← Set.ncard_coe_finset] using hcard (d.gcd n) (d.gcd_dvd_right n)
  _ ≤ d := d.gcd_le_left n hd
