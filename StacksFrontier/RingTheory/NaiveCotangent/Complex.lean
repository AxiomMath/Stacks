module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import StacksCore.Tactic.StacksAttribute

/-! # The naive cotangent complex

The canonical presentation `R[S] → S` of an `R`-algebra `S`, which is the starting point of the
naive cotangent complex.

## References

* [Stacks Project, Tag 07BL](https://stacks.math.columbia.edu/tag/07BL)
-/

@[expose] public section

namespace Stacks.CommAlg.NaiveCotangentComplex

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical map `R[S] → S`, `[s] ↦ s`, is surjective. Here `R[S]` is the polynomial ring
`MvPolynomial S R` over `R` with variables indexed by the elements of `S`, and the map is
`MvPolynomial.aeval id`. -/
theorem canonical_presentation_surjective :
  Function.Surjective (MvPolynomial.aeval (R := R) (id : S → S)) :=
  fun s => ⟨MvPolynomial.X s, MvPolynomial.aeval_X _ _⟩

end Stacks.CommAlg.NaiveCotangentComplex
