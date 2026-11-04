module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.MvPolynomialFiber
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# The fibres of a polynomial presentation have dimension at most its number of variables

Let `R → A` be presented as `R → P = R[x_1, …, x_n] → A` with the second map surjective.  Then
every fibre of `Spec(A) → Spec(R)` has dimension at most `n`: the fibre over a prime `𝔭 ⊂ R` is
`Spec(κ(𝔭) ⊗_R A)`, and base changing the presenting surjection along `R → κ(𝔭)` exhibits
`κ(𝔭) ⊗_R A` as a quotient of `κ(𝔭) ⊗_R P`, which is `n`-dimensional affine space over `κ(𝔭)`.

This is the comparison that the Tor-amplitude statements of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitudeVariableCount` need in
order to be read as instances of the Tor-amplitude clause of [Stacks, Tag 0E9Q], whose hypothesis
is a bound `d` on the dimensions of the fibres of `Spec(A) → Spec(R)` and not a bound on the
number of variables of a presentation: `n` is always such a `d`, so `n ≤ d` implies the clause's
hypothesis at `d`.

Nothing here is about dualizing complexes, and no Noetherian or flatness hypothesis is needed;
only the presentation is.

## Main results

* `Dualizing.PolynomialPresentation.ringKrullDim_fiber_le_variableCount` — the fibre ring
  `κ(𝔭) ⊗_R A` has Krull dimension at most `n`.
* `Dualizing.PolynomialPresentation.relativeDimensionAt_le_variableCount` — the dimension at a
  prime `𝔮 ⊂ A` of the fibre of `Spec(A) → Spec(R)` through `𝔮` is at most `n`.
* `Dualizing.PolynomialPresentation.relativeDimension_le_variableCount` — the relative dimension
  of `A` over `R`, the supremum of those local fibre dimensions, is at most `n`.
* `Dualizing.PolynomialPresentation.relativeDimension_le_of_variableCount_le` — hence `n ≤ d`
  implies that every fibre of `Spec(A) → Spec(R)` has dimension at most `d`.

## Implementation notes

The fibre is `Ideal.Fiber`, i.e. `κ(𝔭) ⊗_R A`, whose spectrum
`PrimeSpectrum.preimageHomeomorphFiber` identifies with the set-theoretic fibre of
`Spec(A) → Spec(R)` over `𝔭`.  Two results carry the work and are reused rather than redone:
`Ideal.ringKrullDim_fiber_mvPolynomial` computes the dimension of the fibre of a polynomial ring
as its number of variables, and `Algebra.relativeDimensionAt_le_ringKrullDim_fiber` bounds the
dimension of a fibre at one of its points by the dimension of the whole fibre.  What is added
here is the surjection between the two fibres, `Algebra.TensorProduct.map` applied to the
identity of `κ(𝔭)` and the presenting surjection, together with the passage from the bound at
each prime to the bound on the supremum that is `Algebra.relativeDimension`.

## References

* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Dualizing

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The fibre of `Spec(A) → Spec(R)` over a prime `𝔭 ⊂ R`, namely `Spec(κ(𝔭) ⊗_R A)`, has
dimension at most the number of variables of any polynomial presentation of `algebraMap R A`:
base changing the presenting surjection `R[x_1, …, x_n] → A` along `R → κ(𝔭)` exhibits
`κ(𝔭) ⊗_R A` as a quotient of the fibre `κ(𝔭) ⊗_R R[x_1, …, x_n]`, whose Krull dimension is `n`
by `Ideal.ringKrullDim_fiber_mvPolynomial`. -/
theorem ringKrullDim_fiber_le_variableCount (p : PolynomialPresentation (algebraMap R A))
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    ringKrullDim (𝔭.Fiber A) ≤ (p.variableCount : WithBot ℕ∞) := by
  refine (ringKrullDim_le_of_surjective
    (Algebra.TensorProduct.map (AlgHom.id R 𝔭.ResidueField)
      (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes)).toRingHom
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id p.surjective)).trans ?_
  rw [𝔭.ringKrullDim_fiber_mvPolynomial (Fin p.variableCount)]
  simp

/-- The dimension of the fibre of `Spec(A) → Spec(R)` at a prime `𝔮 ⊂ A` is at most the number of
variables of any polynomial presentation of `algebraMap R A`: the dimension at a point is at most
the dimension of the whole fibre, which is
`Dualizing.PolynomialPresentation.ringKrullDim_fiber_le_variableCount`. -/
theorem relativeDimensionAt_le_variableCount (p : PolynomialPresentation (algebraMap R A))
    (𝔮 : Ideal A) [𝔮.IsPrime] :
    Algebra.relativeDimensionAt R 𝔮 ≤ (p.variableCount : WithBot ℕ∞) :=
  (Stacks.RegularSequence.FibrewiseLocus.relativeDimensionAt_le_ringKrullDim_fiber R 𝔮).trans
    (p.ringKrullDim_fiber_le_variableCount _)

/-- **Every fibre of `Spec(A) → Spec(R)` has dimension at most the number of variables of a
polynomial presentation of `algebraMap R A`.**  The relative dimension of `A` over `R` is the
supremum over the primes of `A` of the dimension there of the fibre through it, so this is
`Dualizing.PolynomialPresentation.relativeDimensionAt_le_variableCount` at every prime. -/
theorem relativeDimension_le_variableCount (p : PolynomialPresentation (algebraMap R A)) :
    Algebra.relativeDimension R A ≤ (p.variableCount : WithBot ℕ∞) := by
  rw [Algebra.relativeDimension]
  exact iSup_le fun 𝔮 ↦ p.relativeDimensionAt_le_variableCount 𝔮.asIdeal

/-- A bound `d` on the number of variables of a polynomial presentation of `algebraMap R A` is a
bound on the dimensions of all the fibres of `Spec(A) → Spec(R)`.  This is the implication that
lets a Tor-amplitude statement whose hypothesis is `n ≤ d` be read as an instance of the
Tor-amplitude clause of [Stacks, Tag 0E9Q], whose hypothesis is the fibre-dimension bound. -/
theorem relativeDimension_le_of_variableCount_le (p : PolynomialPresentation (algebraMap R A))
    (d : ℕ) (hd : p.variableCount ≤ d) :
    Algebra.relativeDimension R A ≤ (d : WithBot ℕ∞) :=
  p.relativeDimension_le_variableCount.trans (by exact_mod_cast hd)

end PolynomialPresentation

end Dualizing

end
