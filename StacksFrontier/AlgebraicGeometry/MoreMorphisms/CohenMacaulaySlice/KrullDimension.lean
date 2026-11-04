module

public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Killing a maximal regular sequence makes the dimension drop to zero

Let `R` be a Noetherian local ring and let `f₁, …, f_d` be a regular sequence in `R` whose length
is the Krull dimension of `R`.  Then `R / (f₁, …, f_d)` has Krull dimension zero, and so does any
nonzero quotient of `R` in which all the `fᵢ` vanish.

## Main results

* `Stacks.AlgebraicGeometry.ringKrullDim_quotient_eq_zero_of_isRegular`: the quotient by a
  regular sequence of maximal length has dimension zero.
* `Stacks.AlgebraicGeometry.ringKrullDim_eq_zero_of_surjective_of_forall_eq_zero`: the same for
  any nontrivial surjective image killing the sequence.

## Implementation notes

The dimension drop `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` of Mathlib gives
`dim (R / (f)) + d = dim R`, and cancelling the natural number `d` in `WithBot ℕ∞` is
`ENat.WithBot.add_natCast_cancel`.  For the second statement the quotient map factors through
`R / (f)`, so the dimension is at most zero by `ringKrullDim_le_of_surjective`, and it is at
least zero because the target is nontrivial.

## References

* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
-/

@[expose] public section

universe u

namespace Stacks.AlgebraicGeometry

/-- Killing a regular sequence whose length is the Krull dimension leaves a ring of Krull
dimension zero. -/
theorem ringKrullDim_quotient_eq_zero_of_isRegular {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (ss : List R)
    (hreg : RingTheory.Sequence.IsRegular R ss)
    (hlen : (ss.length : WithBot ℕ∞) = ringKrullDim R) :
    ringKrullDim (R ⧸ Ideal.ofList ss) = 0 := by
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ss hreg
  rw [← hlen] at h
  exact ENat.WithBot.add_natCast_cancel.mp (by simpa using h)

/-- A nontrivial surjective image of a Noetherian local ring in which a regular sequence of
maximal length vanishes has Krull dimension zero. -/
theorem ringKrullDim_eq_zero_of_surjective_of_forall_eq_zero {R Q : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [CommRing Q] [Nontrivial Q] (φ : R →+* Q)
    (hφ : Function.Surjective φ) (ss : List R) (hreg : RingTheory.Sequence.IsRegular R ss)
    (hlen : (ss.length : WithBot ℕ∞) = ringKrullDim R) (hkill : ∀ a ∈ ss, φ a = 0) :
    ringKrullDim Q = 0 := by
  have hker : ∀ a ∈ Ideal.ofList ss, φ a = 0 := fun a ha =>
    Ideal.span_le (I := RingHom.ker φ) |>.2 (fun b hb => hkill b hb) ha
  refine le_antisymm ?_ ringKrullDim_nonneg_of_nontrivial
  rw [← ringKrullDim_quotient_eq_zero_of_isRegular ss hreg hlen]
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.lift_surjective_of_surjective _ hker hφ)

end Stacks.AlgebraicGeometry

end
