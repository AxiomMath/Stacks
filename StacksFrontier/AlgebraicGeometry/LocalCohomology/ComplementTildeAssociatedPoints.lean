module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness

/-!
# The associated points of `M̃|_U` are the associated primes of `M` lying in `U`

Let `A` be a Noetherian ring, let `𝔞 ⊆ A` be an ideal, let `U = Spec(A) ∖ V(𝔞)` and let `M` be an
`A`-module. The coherent module `Stacks.LocalCohomology.complementTilde A 𝔞 M` on `U` is the
restriction to `U` of the quasi-coherent module `M̃` on `Spec(A)`, and a point of `U` is an
associated point of it exactly when the corresponding prime is an associated prime of `M`.

Both halves of that are already proved: `Stacks.Divisors.IsAssociatedPoint` is detected by the
prime for `M̃` on an affine scheme, and it is preserved and reflected by restriction along an open
immersion. This file is only the composite, which the algebraization arguments of Stacks chapter
52 need in order to read conditions stated at the associated points of a coherent module on `U`
as conditions at the associated primes of a finite module presenting it.

## Main results

* `Stacks.LocalCohomology.isAssociatedPoint_complementTilde_iff` — the composite, in the
  `Stacks.Divisors.IsAssociatedPoint` spelling.
* `Stacks.LocalCohomology.mem_associatedPoints_complementTilde_iff` — the same as a membership in
  `Stacks.Divisors.associatedPoints` on the left and in Mathlib's `associatedPrimes` on the
  right, which is the shape the algebraization statements are written in.

## Implementation notes

The right-hand side carries no condition confining the prime to `U`: the point `x` is already a
point of `U`, so its prime does not contain `𝔞`, and that is exactly the confinement. A statement
quantified over `PrimeSpectrum A` instead would have to carry `¬ 𝔞 ≤ p` explicitly.

`Stacks.LocalCohomology.complementTilde` unfolds to
`(restrictFunctor (complementZeroLocus A 𝔞).ι).obj (associatedSheaf A M)` and
`Stacks.LocalCohomology.associatedSheaf A M` to `tilde M`, both by `rfl`, which is why
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff` and
`Stacks.LocalCohomology.isAssociatedPoint_tilde_iff` compose with no transport.

## References

* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.CodimensionOneObstruction

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (M : ModuleCat.{u} A)

/-- **The associated points of `M̃|_U` are the associated primes of `M`.** A point of
`U = Spec(A) ∖ V(𝔞)` is an associated point of `Stacks.LocalCohomology.complementTilde A 𝔞 M`
exactly when its prime is an associated prime of `M`. -/
theorem isAssociatedPoint_complementTilde_iff (x : (complementZeroLocus A a : Scheme)) :
    Stacks.Divisors.IsAssociatedPoint (complementTilde A a M) x ↔
      IsAssociatedPrimeStacks A M x.1.asIdeal :=
  (isAssociatedPoint_restrict_iff (complementZeroLocus A a).ι
      ((tilde.functor (CommRingCat.of A)).obj M) x).trans
    (isAssociatedPoint_tilde_iff A M x.1)

/-- **The associated points of `M̃|_U` are the associated primes of `M`**, as a membership
statement on both sides. This is the shape the algebraization statements of Stacks chapter 52
consume: their sheaf-level conditions quantify over
`Stacks.Divisors.associatedPoints (complementTilde A 𝔞 M)` and their ring-level conditions over
`associatedPrimes A M`. -/
theorem mem_associatedPoints_complementTilde_iff (x : (complementZeroLocus A a : Scheme)) :
    x ∈ Stacks.Divisors.associatedPoints (complementTilde A a M) ↔
      x.1.asIdeal ∈ associatedPrimes A M :=
  (isAssociatedPoint_complementTilde_iff A a M x).trans
    (isAssociatedPrimeStacks_iff_mem_associatedPrimes _)

end Stacks.LocalCohomology

end
