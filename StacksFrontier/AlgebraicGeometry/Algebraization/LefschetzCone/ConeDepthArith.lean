module

public import Mathlib.Order.KrullDimension
public import Mathlib.Tactic.NormNum

/-!
# The arithmetic of "either the depth goes up by one or the dimension"

On the punctured cone `U → P` over a projective scheme, a point `y` of `U ∩ Y` over `q ∈ Q` is
either the generic point of its fibre, where the depth of the stalk is at least that at `q` and
the distance to the vertex is at least `dim({q}‾) + 1`, or a closed point of its fibre, where the
depth is at least that at `q` plus one and the distance at least `dim({q}‾)`. Combined with
`depth(ℱ''_q) ≥ 1` when `dim({q}‾) ≤ 1`, `depth(ℱ''_q) ≥ 2` when `dim({q}‾) = 0`, and the distance
being always at least one, this gives `depth + δ ≥ 3`: the arithmetic of the proof of Stacks 0EL5.

## Main results

* `Stacks.LefschetzCone.three_le_add_of_fibre`
-/

@[expose] public section

namespace Stacks.LefschetzCone

/-- **`depth + δ ≥ 3` from the fibre dichotomy.** -/
theorem three_le_add_of_fibre (dy dq δ e : ℕ∞) (generic : Prop)
    (hdepth : generic ∨ dq + 1 ≤ dy) (hdepth' : dq ≤ dy)
    (hdist : (generic → e + 1 ≤ δ) ∧ e ≤ δ) (hδ : 1 ≤ δ)
    (hT : e ≤ 1 → 1 ≤ dq) (hT' : e ≤ 0 → 2 ≤ dq) : 3 ≤ dy + δ := by
  have key : 3 ≤ dy ∨ (2 ≤ dy ∧ 1 ≤ δ) ∨ (1 ≤ dy ∧ 2 ≤ δ) ∨ 3 ≤ δ := by
    by_cases he0 : e ≤ 0
    · have h2 := hT' he0
      rcases hdepth with hg | hc
      · exact Or.inr (Or.inl ⟨h2.trans hdepth', hδ⟩)
      · exact Or.inl ((show (3 : ℕ∞) ≤ 2 + 1 by norm_num).trans ((add_le_add_left h2 1).trans hc))
    · by_cases he1 : e ≤ 1
      · have h1 := hT he1
        have he : e = 1 := le_antisymm he1 (Order.one_le_iff_pos.2 (lt_of_not_ge he0))
        rcases hdepth with hg | hc
        · refine Or.inr (Or.inr (Or.inl ⟨h1.trans hdepth', ?_⟩))
          have := hdist.1 hg
          rw [he] at this
          exact this
        · exact Or.inr (Or.inl ⟨(show (2 : ℕ∞) ≤ 1 + 1 by norm_num).trans
            ((add_le_add_left h1 1).trans hc), hδ⟩)
      · have he2 : 2 ≤ e := Order.add_one_le_of_lt (lt_of_not_ge he1)
        rcases hdepth with hg | hc
        · exact Or.inr (Or.inr (Or.inr ((show (3 : ℕ∞) ≤ 2 + 1 by norm_num).trans
            ((add_le_add_left he2 1).trans (hdist.1 hg)))))
        · exact Or.inr (Or.inr (Or.inl ⟨le_add_self.trans hc, he2.trans hdist.2⟩))
  rcases key with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · exact h.trans le_self_add
  · exact (add_le_add h1 h2).trans' (by norm_num)
  · exact (add_le_add h1 h2).trans' (by norm_num)
  · exact h.trans le_add_self

end Stacks.LefschetzCone

end
