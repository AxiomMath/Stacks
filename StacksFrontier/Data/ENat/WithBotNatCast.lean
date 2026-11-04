module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Order.WithBot

/-!
# Casts of natural numbers in `WithBot ℕ∞`

Mathlib's `ENat.natCast_ne_top` is the statement one level down, in `ℕ∞`; this file gives the
`WithBot ℕ∞` form.

## Main results

* `natCast_ne_top_withBot`
* `eq_natCast_unbotD_toNat`
-/

@[expose] public section

/-- A natural number, cast into `WithBot ℕ∞`, is not `⊤`. -/
theorem natCast_ne_top_withBot (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := fun hn ↦
  ENat.natCast_ne_top n (WithBot.coe_injective
    (hn : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞)))

/-- A dimension in `WithBot ℕ∞` that is neither `⊥` nor `⊤` is the cast of a natural number. -/
theorem eq_natCast_unbotD_toNat {d : WithBot ℕ∞} (hbot : d ≠ ⊥) (htop : d ≠ ⊤) :
    d = ((d.unbotD 0).toNat : WithBot ℕ∞) := by
  cases d with
  | bot => exact (hbot rfl).elim
  | coe d =>
    have hd : d ≠ ⊤ := by simpa using htop
    simp only [WithBot.unbotD_coe]
    simpa using (congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat hd)).symm

end
