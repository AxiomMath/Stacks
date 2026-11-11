module

public import StacksCore.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic groups of order dividing `n`

The complete form of Stacks 09HX: a group `G` with `x ^ n = 1` for all `x` in which, for every
`d ∣ n`, at most `d` elements satisfy `x ^ d = 1`, is cyclic of order dividing `n`. The
cardinality bound is stated with `Set.encard`, so finiteness of `G` is deduced rather than
assumed.

The registration of 09HX on `isCyclic_of_card_pow_eq_one_le_of_dvd` in
`StacksCore/GroupTheory/SpecificGroups/Cyclic.lean` is the weaker form (it assumes `[Finite G]` and
concludes only `IsCyclic G`); it is left unchanged there because `StacksCore/` is the reviewed tree.
-/

@[expose] public section

/-- A group of exponent dividing `n` in which, for every `d ∣ n`, at most `d` elements satisfy
`x ^ d = 1` is cyclic of order dividing `n`. The cardinality bound is stated with `Set.encard`,
so finiteness of `G` is deduced rather than assumed. -/
@[stacks 09HX "cyclic of order dividing n; finiteness deduced", to_additive
  isAddCyclic_and_card_dvd_of_encard_nsmul_eq_zero_le_of_dvd
/-- An additive group of exponent dividing `n` in which, for
every `d ∣ n`, at most `d` elements satisfy `d • x = 0` is cyclic of order dividing `n`. -/]
theorem isCyclic_and_card_dvd_of_encard_pow_eq_one_le_of_dvd
    {G : Type*} [Group G] {n : ℕ} (hpow : ∀ x : G, x ^ n = 1)
    (hcard : ∀ d, d ∣ n → {x : G | x ^ d = 1}.encard ≤ d) :
    IsCyclic G ∧ Nat.card G ∣ n := by
  have huniv : {x : G | x ^ n = 1} = Set.univ := Set.eq_univ_of_forall hpow
  have hfin : (Set.univ : Set G).Finite :=
    Set.finite_of_encard_le_coe (huniv ▸ hcard n dvd_rfl)
  have : Finite G := Set.finite_univ_iff.mp hfin
  have hcyc : IsCyclic G := isCyclic_of_card_pow_eq_one_le_of_dvd hpow fun d hd ↦ by
    have h := hcard d hd
    rw [← (Set.toFinite {x : G | x ^ d = 1}).cast_ncard_eq] at h
    exact_mod_cast h
  refine ⟨hcyc, ?_⟩
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
