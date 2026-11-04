module

public import Mathlib.Order.KrullDimension

/-!
# Height plus coheight is at most the Krull dimension

In a preorder a chain descending from a point and a chain ascending from it splice at the point
into a single chain, so the height and the coheight of a point add up to at most the Krull
dimension of the preorder. Mathlib records the supremum form of this,
`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`; this file records the inequality at a
single point, which is the form consumers apply.

## Main results

* `Order.height_add_coheight_le_krullDim`: `height x + coheight x ≤ krullDim α`.
-/

@[expose] public section

namespace Order

/-- In a preorder the height and the coheight of a point add up to at most the Krull dimension:
a chain below `x` and a chain above `x` splice at `x`. -/
theorem height_add_coheight_le_krullDim {α : Type*} [Preorder α] (x : α) :
    (Order.height x : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) ≤ Order.krullDim α := by
  have : Nonempty α := ⟨x⟩
  rw [← WithBot.coe_add, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) x)

end Order
