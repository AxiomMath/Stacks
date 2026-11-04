module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic

/-!
# The two spellings of "associated point" agree

This repository carries two definitions of an associated point of an `𝒪_X`-module:
`Stacks.AlgebraicGeometry.AssociatedPointsMono.IsAssociatedPoint`, used by the foundations tree,
and `Stacks.Divisors.IsAssociatedPoint`, which carries the tag of Stacks 02OJ. They are the same
condition — the maximal ideal of `𝒪_{X,x}` is an associated prime of the stalk, in the
exact-annihilator sense of Tag 00LA — written against two spellings of the stalk, and are
definitionally equal. This file records that, and transports the bridge of
`AssociatedPointPrime.Basic` to the tagged spelling.

## Main results

* `isAssociatedPoint_iff_divisors` and `associatedPoints_eq_divisors`: the two notions, and the
  two sets, coincide.
* `divisorsIsAssociatedPoint_iff_mem_associatedPrimes`: the affine-open bridge for the tagged
  spelling, stated with Mathlib's `associatedPrimes`.

## Implementation notes

The comparison
`AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian`
(Stacks Tag 02OK) states the same equivalence with the ring side written as
`IsAssociatedPrimeStacks`, the exact-annihilator notion of Tag 00LA. The statements here use
Mathlib's radical-based `associatedPrimes` instead, because that is the notion the
algebraic result
`Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one`
consumes; the two ring-side notions are reconciled in `AssociatedPointPrime.Ring`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointsMono

universe u

namespace Stacks.AlgebraicGeometry.AssociatedPointPrime

variable {X : Scheme.{u}}

/-- The foundations-tree notion of an associated point and the notion carrying the tag of Stacks
02OJ are the same condition. -/
theorem isAssociatedPoint_iff_divisors (F : X.Modules) (x : X) :
    IsAssociatedPoint F x ↔ Stacks.Divisors.IsAssociatedPoint F x :=
  Iff.rfl

/-- The two sets of associated points coincide. -/
theorem associatedPoints_eq_divisors (F : X.Modules) :
    associatedPoints F = Stacks.Divisors.associatedPoints F :=
  rfl

/-- **The affine-open bridge for the tagged spelling.** A point of an affine open is an
associated point of a quasi-coherent module, in the sense tagged with Stacks 02OJ, exactly when
the prime of that point is an associated prime of the sections, in Mathlib's sense. -/
theorem divisorsIsAssociatedPoint_iff_mem_associatedPrimes [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Stacks.Divisors.IsAssociatedPoint F x ↔
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) :=
  isAssociatedPoint_iff_mem_associatedPrimes F hU hx

end Stacks.AlgebraicGeometry.AssociatedPointPrime

end
