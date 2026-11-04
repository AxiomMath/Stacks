module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbolProd

/-!
# Permuting the entries of a Milnor symbol costs only a sign

Degree-one symbols in the Milnor K-ring anticommute, `{u} {v} + {v} {u} = 0`
(`milnorKSymbol_mul_add_mul_comm`). So reordering the entries of a symbol product
`{u_1, …, u_r}` changes it by at most a sign:

`{u_{σ 1}, …, {u_{σ r}} = ± {u_1, …, u_r}`.

This file proves that, in the form a subgroup argument consumes: an additive subgroup containing
the symbol of one ordering contains the symbol of every ordering
(`milnorKSymbolProd_mem_of_perm`), a subgroup being closed under negation.

That is what lets an induction which must operate on two particular entries of a symbol — for
instance the Bass–Tate reduction, which applies
`Stacks.Chow.milnorKSymbol_mul_of_add_eq'` to two monic entries of equal degree — assume those
entries are the first two, without carrying a permutation through the statement.

## Main results

* `Stacks.Chow.milnorKSymbolProd_swap_cons` — swapping the first two entries negates the symbol.
* `Stacks.Chow.milnorKSymbolProd_perm` — a permutation changes the symbol by at most a sign.
* `Stacks.Chow.milnorKSymbolProd_mem_of_perm` — **the subgroup form.**

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public section

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- **Swapping the first two entries of a symbol negates it.** This is the anticommutation of
degree-one symbols, `{u} {v} + {v} {u} = 0`, read on a symbol product. -/
theorem milnorKSymbolProd_swap_cons (u v : kˣ) (l : List kˣ) :
    milnorKSymbolProd k (u :: v :: l) = -milnorKSymbolProd k (v :: u :: l) := by
  rw [milnorKSymbolProd_cons, milnorKSymbolProd_cons, milnorKSymbolProd_cons,
    milnorKSymbolProd_cons, ← mul_assoc, ← mul_assoc,
    eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_add_mul_comm (k := k) u v), neg_mul]

/-- **A permutation of the entries changes a symbol product by at most a sign.** -/
theorem milnorKSymbolProd_perm {l l' : List kˣ} (h : l.Perm l') :
    milnorKSymbolProd k l = milnorKSymbolProd k l' ∨
      milnorKSymbolProd k l = -milnorKSymbolProd k l' := by
  induction h with
  | nil => exact Or.inl rfl
  | cons x _ ih =>
      rcases ih with hp | hp
      · exact Or.inl (by rw [milnorKSymbolProd_cons, milnorKSymbolProd_cons, hp])
      · exact Or.inr (by rw [milnorKSymbolProd_cons, milnorKSymbolProd_cons, hp, mul_neg])
  | swap x y l => exact Or.inr (milnorKSymbolProd_swap_cons y x l)
  | trans _ _ ih₁ ih₂ =>
      rcases ih₁ with hp₁ | hp₁ <;> rcases ih₂ with hp₂ | hp₂
      · exact Or.inl (hp₁.trans hp₂)
      · exact Or.inr (hp₁.trans hp₂)
      · exact Or.inr (by rw [hp₁, hp₂])
      · exact Or.inl (by rw [hp₁, hp₂, neg_neg])

/-- **An additive subgroup containing the symbol of one ordering of a list contains the symbol of
every ordering.** -/
theorem milnorKSymbolProd_mem_of_perm {H : AddSubgroup (MilnorKRing k)} {l l' : List kˣ}
    (h : l.Perm l') (hl' : milnorKSymbolProd k l' ∈ H) : milnorKSymbolProd k l ∈ H := by
  rcases milnorKSymbolProd_perm h with hp | hp
  · rw [hp]; exact hl'
  · rw [hp]; exact neg_mem hl'

end Stacks.Chow

end
