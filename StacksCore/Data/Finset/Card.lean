module

public import Mathlib.Data.Finset.Card

/-! # Lemmas about the cardinality of a finset -/

@[expose] public section

theorem Finset.card_eq_one_iff_of_mem {α : Type*} {s : Finset α} {x : α} (hx : x ∈ s) :
    s.card = 1 ↔ s = {x} := by rw [card_eq_one]; grind
