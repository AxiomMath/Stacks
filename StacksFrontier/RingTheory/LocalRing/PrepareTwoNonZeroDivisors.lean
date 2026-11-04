module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalRing.InvertibleSpanPairBlowUp

/-!
# Preparing two nonzerodivisors in a one-dimensional Noetherian local ring

Over a Noetherian local ring of Krull dimension one, two nonzerodivisors `a` and `b` become
`t * a'` and `t * b'` with `t`, `a'` and `b'` nonzerodivisors and `(a', b') = (1)`, after a finite
ring extension which is injective on the base and whose quotient by the base is annihilated by a
power of the maximal ideal.

## Main results

* `Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors` proves
  `AlgebraicGeometry.FiniteExtensionPreparingTwoNonzerodivisors`.
* `Stacks.PrepareNonZeroDivisors.exists_finiteExtension_factorization_of_ringKrullDim_eq_one` is
  that statement written out.

## References

* [Stacks Project, Tag 02Q7](https://stacks.math.columbia.edu/tag/02Q7)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.PrepareNonZeroDivisors

/-- Two nonzerodivisors in a one-dimensional Noetherian local ring acquire a common
nonzerodivisor factor with comaximal cofactors in a finite ring extension whose quotient by the
base is annihilated by a power of the maximal ideal. -/
theorem finiteExtensionPreparingTwoNonzerodivisors :
    AlgebraicGeometry.FiniteExtensionPreparingTwoNonzerodivisors.{u} :=
  finiteExtensionPreparingTwoNonzerodivisors_of_invertibleSpanPair
    invertibleSpanPairAfterFiniteExtension

/-- **Stacks Project, Tag 02Q7.** Let `R` be a one-dimensional Noetherian local ring and let `a`
and `b` be nonzerodivisors. There is a finite ring extension in which they have a common
nonzerodivisor factor and their residual factors generate the unit ideal; moreover, a power of the
maximal ideal annihilates the quotient by `R`. -/
@[stacks 02Q7]
theorem exists_finiteExtension_factorization_of_ringKrullDim_eq_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (a b : R)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Finite R S ∧
      Function.Injective (algebraMap R S) ∧
      (∃ n : ℕ, maximalIdeal R ^ n ≤
        Module.annihilator R (S ⧸ (Algebra.linearMap R S).range)) ∧
      ∃ t a' b' : S,
        t ∈ nonZeroDivisors S ∧
        a' ∈ nonZeroDivisors S ∧
        b' ∈ nonZeroDivisors S ∧
        algebraMap R S a = t * a' ∧
        algebraMap R S b = t * b' ∧
        Ideal.span ({a', b'} : Set S) = ⊤ :=
  finiteExtensionPreparingTwoNonzerodivisors R hdim a b ha hb

end Stacks.PrepareNonZeroDivisors

end
