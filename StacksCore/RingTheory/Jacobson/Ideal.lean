module

public import Mathlib.RingTheory.Jacobson.Ideal

/-! # Ideals contained in the Jacobson radical

Stacks tag 0AME: for an ideal `I` of a ring `R`, containment in the Jacobson radical is
equivalent to every element of `1 + I` being a unit; and when that holds, an element of `R`
whose image in `R/I` is a unit was already a unit in `R`.

Mathlib has both facts *elementwise* rather than at the level of an ideal:
`Ideal.mem_jacobson_bot` characterises membership in `jacobson ⊥` by `∀ y, IsUnit (x * y + 1)`,
and `Ideal.isUnit_of_sub_one_mem_jacobson_bot` gives the second clause for a single element.
What is added here is the ideal-level statement the tag asserts. The quantifier over `y` in
Mathlib's version is what makes the ideal form fall out: an ideal absorbs multiplication, so
testing `1 + x` for `x ∈ I` already tests `1 + xy` for every `y`.

The Jacobson radical is spelled `Ring.jacobson R`, which `Ideal.jacobson_bot` identifies with
`Ideal.jacobson (⊥ : Ideal R)`; the lemmas cited above are stated in the latter form, so both
proofs below start by moving between the two.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ideal

/-- **Stacks 0AME**, (1) ⇔ (2): an ideal is contained in the Jacobson radical if and only if
every element of `1 + I` is a unit.

Forwards is `Ideal.mem_jacobson_bot` at `y = 1`. Backwards uses that `I` is an ideal: to place
`x ∈ I` in the radical one must invert `1 + x * y` for every `y`, and `x * y` is again in `I`. -/
@[stacks 0AME "(1) ⇔ (2)"]
theorem le_ringJacobson_iff_isUnit_one_add (I : Ideal R) :
    I ≤ Ring.jacobson R ↔ ∀ x ∈ I, IsUnit (1 + x) := by
  rw [← Ideal.jacobson_bot]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ Ideal.mem_jacobson_bot.2 fun y ↦ ?_⟩
  · simpa [add_comm] using (Ideal.mem_jacobson_bot.1 (h hx)) 1
  · simpa [add_comm] using h _ (I.mul_mem_right y hx)

/-- **Stacks 0AME**, the closing clause: if `I` is contained in the Jacobson radical, then an
element of `R` whose image in `R ⧸ I` is a unit is itself a unit.

Given a right inverse `y` mod `I`, the difference `x * y - 1` lies in `I` and hence in the
radical, so `x * y` is a unit by `Ideal.isUnit_of_sub_one_mem_jacobson_bot`; a factor of a unit
in a commutative ring is a unit. -/
@[stacks 0AME "in this case a unit mod I is a unit"]
theorem isUnit_of_isUnit_quotient_mk (I : Ideal R) (h : I ≤ Ring.jacobson R) (x : R)
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hy
  exact isUnit_of_mul_isUnit_left <| Ideal.isUnit_of_sub_one_mem_jacobson_bot _ <|
    Ideal.jacobson_bot (R := R) ▸ h hy

end Ideal
