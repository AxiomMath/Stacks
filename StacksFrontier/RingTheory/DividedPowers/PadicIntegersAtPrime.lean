module

public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# `ℤ_[p]` is an algebra over `ℤ_(p)`

The universal properties of divided power algebras in this library — the `p`-adic completion of a
divided power ring, `DividedPowers.existsUnique_dPMorphism_from_completion`, and the divided power
polynomial algebras built on it — carry the hypothesis
`[Algebra (DividedPowers.IntegersAtPrime p) R]`, the localization `ℤ_(p)` of the integers at `p`
being where the coefficients `n!/(i! j!)` of the divided power identities live.

For the base `ℤ_[p]` of the two counterexamples of [Stacks, Section 60.22] that hypothesis is
satisfied, and this module records it: an integer prime to `p` has `p`-adic norm one, hence is a
unit of `ℤ_[p]`, so `ℤ → ℤ_[p]` inverts the complement of the prime ideal `(p) ⊆ ℤ` and factors
through its localization.

## Main definitions

* `DividedPowers.padicIntAlgebraAtPrime` — the `ℤ_(p)`-algebra structure on `ℤ_[p]`.

## References

* [Stacks Project, Tag 07GM](https://stacks.math.columbia.edu/tag/07GM)
-/

@[expose] public noncomputable section

namespace DividedPowers

/-- **`ℤ_[p]` is a `ℤ_(p)`-algebra.**  An integer prime to `p` has `p`-adic norm `1`, hence is a
unit of `ℤ_[p]`, so the inclusion `ℤ → ℤ_[p]` inverts the complement of the prime ideal
`(p) ⊆ ℤ` and factors through the localization `ℤ_(p)`. -/
@[instance_reducible]
def padicIntAlgebraAtPrime (p : ℕ) [Fact p.Prime] : Algebra (IntegersAtPrime p) ℤ_[p] := by
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  refine RingHom.toAlgebra (IsLocalization.lift (M := (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl)
    (g := Int.castRingHom ℤ_[p]) ?_)
  intro y
  have hy : ¬ ((p : ℤ) ∣ (y : ℤ)) := fun hdvd ↦ y.2 (Ideal.mem_span_singleton.mpr hdvd)
  rw [PadicInt.isUnit_iff]
  change ‖((y : ℤ) : ℤ_[p])‖ = 1
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact hy

end DividedPowers

end
