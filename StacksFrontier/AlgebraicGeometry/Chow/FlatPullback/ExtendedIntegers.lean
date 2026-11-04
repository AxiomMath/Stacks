module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary

/-!
# Translation in the extended integers

The delta-dimension of a scheme over the base of chapter 42 of the Stacks Project is a supremum
over irreducible components, hence valued in the extended integers `EInt = WithBot (WithTop ℤ)`
rather than in `ℤ`. The dimension formulas of that chapter add an integer to such a supremum —
the relative dimension of a flat morphism, or `-1` for a divisor — so they need the two facts
collected here: that the embedding `ℤ → EInt` is additive, and that translation by a fixed
integer, being an order isomorphism of `EInt`, commutes with suprema.

## Main definitions

* `Stacks.Chow.eintAddRight` — translation by a fixed integer, as an order isomorphism of the
  extended integers.

## Main results

* `Stacks.Chow.coe_add_coe_eq_coe_add` — the embedding `ℤ → EInt` is additive.
* `Stacks.Chow.iSup_add_coe` — translation by an integer commutes with suprema.
-/

@[expose] public noncomputable section

open TopologicalSpace

namespace Stacks.Chow

/-- Translation by a fixed integer, as an order isomorphism of the extended integers: it is the
order isomorphism `· + n` of `ℤ`, extended first by a top element and then by a bottom one,
each of which translation fixes. -/
def eintAddRight (n : ℤ) : EInt ≃o EInt :=
  ((OrderIso.addRight n).withTopCongr).withBotCongr

/-- `eintAddRight n` sends an extended integer `a` to `a + n`. -/
@[simp]
theorem eintAddRight_apply (n : ℤ) (a : EInt) : eintAddRight n a = a + (n : EInt) := by
  cases a with
  | none => rfl
  | some a =>
    cases a with
    | top => rfl
    | coe a => rfl

/-- Translation by an integer commutes with suprema in the extended integers. -/
theorem iSup_add_coe {ι : Sort*} (f : ι → EInt) (n : ℤ) :
    (⨆ i, f i) + (n : EInt) = ⨆ i, (f i + (n : EInt)) := by
  have h := (eintAddRight n).map_iSup f
  simpa only [eintAddRight_apply] using h

/-- The embedding of the integers into the extended integers is additive. -/
theorem coe_add_coe_eq_coe_add (a b : ℤ) : ((a + b : ℤ) : EInt) = (a : EInt) + (b : EInt) := by
  show (↑(↑(a + b) : WithTop ℤ) : WithBot (WithTop ℤ)) =
    (↑(↑a : WithTop ℤ) : WithBot (WithTop ℤ)) + (↑(↑b : WithTop ℤ) : WithBot (WithTop ℤ))
  rw [← WithBot.coe_add, ← WithTop.coe_add]

end Stacks.Chow

end
