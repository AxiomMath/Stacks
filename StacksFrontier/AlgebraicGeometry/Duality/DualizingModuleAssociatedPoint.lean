module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.RingTheory.Dualizing.AssociatedPrimeRegular
import StacksCore.Tactic.StacksAttribute

/-!
# A nonzerodivisor at an associated point of a dualizing module is a unit

Let `X` be a locally Noetherian scheme and let `ω` be a quasi-coherent `𝒪_X`-module whose
complex `ω[n]` in some degree is a dualizing complex on `X`. If `x` is an associated point of
`ω` ([Stacks, Tag 02OJ]), then every nonzerodivisor of the local ring `𝒪_{X, x}` is a unit
there.

This is the local form of the statement that a dualizing module has no associated point on an
effective Cartier divisor: on the divisor the local equation is a nonzerodivisor and not a unit.

## Main results

* `Stacks.Duality.isUnit_of_isSMulRegular_of_isAssociatedPoint`.

## Implementation notes

The stalk `ω_x` is a dualizing module over `𝒪_{X, x}`
(`Stacks.Duality.isDualizingComplex_single_stalk`), and being an associated point means the
maximal ideal is an associated prime of that stalk, so
`Dualizing.not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal` applies: the ring is then
zero-dimensional and the maximal ideal consists of zerodivisors.

Associated primes come in two spellings — the exact annihilator of
`StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs` which the scheme-level associated points use,
and the radical annihilator of Mathlib's `IsAssociatedPrime` — and the first implies the second
with no hypothesis, by
`Stacks.RingTheory.AssociatedPrimeStacks.isAssociatedPrime_of_isAssociatedPrimeStacks`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **At an associated point of a dualizing module every nonzerodivisor of the local ring is a
unit.** -/
theorem isUnit_of_isSMulRegular_of_isAssociatedPoint (ω : X.Modules) [ω.IsQuasicoherent] (n : ℤ)
    (hω : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω))
    {x : X} (hx : Stacks.Divisors.IsAssociatedPoint ω x)
    {t : X.presheaf.stalk x} (ht : IsSMulRegular (X.presheaf.stalk x) t) :
    IsUnit t := by
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  by_contra hunit
  refine Dualizing.not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal
    (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x))
    (isDualizingComplex_single_stalk ω n hω x) ?_
    ((IsLocalRing.mem_maximalIdeal t).mpr hunit) ht
  exact Stacks.RingTheory.AssociatedPrimeStacks.isAssociatedPrime_of_isAssociatedPrimeStacks hx

end Stacks.Duality

end
