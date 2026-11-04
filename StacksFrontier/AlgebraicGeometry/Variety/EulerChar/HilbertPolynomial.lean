module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The Hilbert polynomial of a coherent sheaf on projective space

The Hilbert polynomial of a coherent sheaf on projective space over a field is the
integer-valued function sending a twist degree to its Euler characteristic.

## Main definitions

* `AlgebraicGeometry.hilbertPolynomial` is the Euler characteristic of each twist.

## Implementation notes

The source defines the Hilbert polynomial first as a function on the integers.  Here the Euler
characteristic is written as its defining alternating sum of the dimensions of sheaf
cohomology. This form does not require supplying separate properness and coherence instances
merely to form the function. The twist is the pullback of the integral projective-space twist.

## References

* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The Hilbert polynomial, viewed as an integer-valued function of the twist
degree, of a coherent sheaf on projective space over a field. -/
@[stacks 08AD,
  sga "6 XIII 6.1" "partial"]
noncomputable def hilbertPolynomial (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] : ℤ → ℤ :=
  fun d => ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
    (Module.finrank k (cohomologyOverField k
      (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
      (projectiveTwist n F d) i) : ℤ)

end AlgebraicGeometry
