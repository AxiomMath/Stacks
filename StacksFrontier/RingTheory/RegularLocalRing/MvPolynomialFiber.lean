module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibres of a polynomial ring

Let `R` be a commutative ring and `𝔭` a prime of `R`. The fibre of `R → R[x_i, i ∈ ι]` over `𝔭`
is the polynomial ring `κ(𝔭)[x_i, i ∈ ι]` over a field, by
`MvPolynomial.algebraTensorAlgEquiv`. This file records what that gives: the fibre is a regular
ring, it is a domain — so its spectrum is irreducible, hence equidimensional — and for finite `ι`
its Krull dimension is the number of variables.

None of this asks anything of `R`: the residue field contributes `0` to the dimension whatever
`R` is, and regularity and integrality of a polynomial ring over a field are absolute.

## Main results

* `Ideal.isRegularRing_fiber_mvPolynomial`, `Ideal.isDomain_fiber_mvPolynomial`,
  `Ideal.ringKrullDim_fiber_mvPolynomial`: the fibre is a regular ring, a domain, and of
  dimension `#ι`.
* `Ideal.isMaximalCohenMacaulay_localization_fiber_mvPolynomial`: every local ring of the fibre is
  maximal Cohen-Macaulay over itself, being regular local ([StacksProject 00NQ]).
* `Ideal.equidimensional_primeSpectrum_fiber_mvPolynomial`: the spectrum of the fibre is
  equidimensional.
* `Ideal.isMaximalCohenMacaulay_and_equidimensional_and_ringKrullDim_fiber_mvPolynomial`: for
  `n` variables (`ι = Fin n`), every local ring of the fibre is maximal Cohen-Macaulay, the
  spectrum of the fibre is equidimensional, and the fibre has dimension `n`.

The bundled form is stated with no nontriviality hypothesis on the fibre: a polynomial ring over
a field is never the zero ring.

## References

* [StacksProject 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [StacksProject 00RB](https://stacks.math.columbia.edu/tag/00RB)
* [StacksProject 00RC](https://stacks.math.columbia.edu/tag/00RC)

## Tags

polynomial ring, fibre, residue field, regular ring, Cohen-Macaulay ring, equidimensional,
Krull dimension
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **The fibres of a polynomial ring are regular.** The fibre `κ(𝔭) ⊗_R R[ι]` of the polynomial
ring `R[ι]` over a prime `𝔭` of `R` is a regular ring, being the polynomial ring `κ(𝔭)[ι]` over a
field.

This is the mixed-characteristic form of `MvPolynomial.isRegularRing_of_isRegularRing`: the base
`R` is arbitrary, and regularity is asserted of the fibres rather than of `R[ι]` itself. -/
@[ega "0 17.3.7" "coefficient ring a field"]
theorem isRegularRing_fiber_mvPolynomial (ι : Type*) [Finite ι] :
    IsRegularRing (p.Fiber (MvPolynomial ι R)) :=
  IsRegularRing.of_ringEquiv
    (MvPolynomial.algebraTensorAlgEquiv R p.ResidueField (σ := ι)).symm.toRingEquiv

/-- **The fibres of a polynomial ring are domains**, being polynomial rings over a field. -/
theorem isDomain_fiber_mvPolynomial (ι : Type*) : IsDomain (p.Fiber (MvPolynomial ι R)) :=
  let e := (MvPolynomial.algebraTensorAlgEquiv R p.ResidueField (σ := ι)).toRingEquiv
  e.injective.isDomain e

/-- **The spectrum of a fibre of a polynomial ring is equidimensional.** The fibre is a domain
(`Ideal.isDomain_fiber_mvPolynomial`), so its spectrum is irreducible and therefore has a single
irreducible component. -/
theorem equidimensional_primeSpectrum_fiber_mvPolynomial (ι : Type*) :
    TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber (MvPolynomial ι R))) :=
  have := p.isDomain_fiber_mvPolynomial ι
  .of_preirreducibleSpace _

/-- **The fibres of a polynomial ring in `#ι` variables have dimension `#ι`.** The fibre
`κ(𝔭) ⊗_R R[ι]` is the polynomial ring `κ(𝔭)[ι]` over a field, whose Krull dimension is the
number of variables.

Companion of `MvPolynomial.ringKrullDim_of_isNoetherianRing`, from which it differs in asking
nothing of `R`. -/
theorem ringKrullDim_fiber_mvPolynomial (ι : Type*) [Finite ι] :
    ringKrullDim (p.Fiber (MvPolynomial ι R)) = (Nat.card ι : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.algebraTensorAlgEquiv R p.ResidueField (σ := ι)).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- **The local rings of the fibres of a polynomial ring are regular local**, the fibre being the
regular ring `κ(𝔭)[ι]` (`Ideal.isRegularRing_fiber_mvPolynomial`).

This is the form the resolution argument of Theorem 00RC needs in its own right: the step which
forces the `n`-th syzygy to be free on the fibre needs the fibre's local rings to have finite
global dimension, and that is regularity ([StacksProject 00OC]). -/
theorem isRegularLocalRing_localization_fiber_mvPolynomial (ι : Type*) [Finite ι]
    (Q : Ideal (p.Fiber (MvPolynomial ι R))) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) :=
  have := p.isRegularRing_fiber_mvPolynomial ι
  IsRegularRing.isRegularLocalRing_localization Q

/-- **The local rings of the fibres of a polynomial ring are Cohen-Macaulay.** Every local ring
`(κ(𝔭) ⊗_R R[ι])_Q` of a fibre of the polynomial ring `R[ι]` is maximal Cohen-Macaulay over
itself, the fibre being regular and a regular local ring being Cohen-Macaulay
([StacksProject 00NQ]). -/
theorem isMaximalCohenMacaulay_localization_fiber_mvPolynomial (ι : Type*) [Finite ι]
    (Q : Ideal (p.Fiber (MvPolynomial ι R))) [Q.IsPrime] :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q) :=
  have := p.isRegularLocalRing_localization_fiber_mvPolynomial ι Q
  (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    (Localization.AtPrime Q)).2

/-- **The local rings of a fibre of `R → R[x_1, …, x_n]` have dimension at most `n`.** The
dimension of `(κ(𝔭) ⊗_R R[x_1, …, x_n])_Q` is the height of `Q`, which is at most the dimension
`n` of the fibre (`Ideal.ringKrullDim_fiber_mvPolynomial`). -/
theorem ringKrullDim_localization_fiber_mvPolynomial_le {n : ℕ}
    (Q : Ideal (p.Fiber (MvPolynomial (Fin n) R))) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ (n : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
  refine le_trans Ideal.height_le_ringKrullDim_of_isPrime ?_
  simpa using (p.ringKrullDim_fiber_mvPolynomial (Fin n)).le

/-- **The fibre hypothesis of Lemma 00RB for a polynomial ring.** For `S = R[x_1, …, x_n]` every
fibre of `R → S` is Cohen-Macaulay and equidimensional of dimension `n`: it is the polynomial ring
`κ(𝔭)[x_1, …, x_n]` over a field, hence a regular domain of dimension `n`, so its spectrum is
irreducible and each of its local rings is regular local and therefore maximal Cohen-Macaulay
over itself.

This is the hypothesis `hfib` of
`Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional`
with `d = n`, and it is the only fibre input Theorem 00RC needs, which applies Lemma 00RB to a
polynomial ring over `R`. No nontriviality guard is needed. -/
theorem isMaximalCohenMacaulay_and_equidimensional_and_ringKrullDim_fiber_mvPolynomial (n : ℕ) :
    (∀ (Q : Ideal (p.Fiber (MvPolynomial (Fin n) R))) [Q.IsPrime],
        Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
      TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R))) ∧
      ringKrullDim (p.Fiber (MvPolynomial (Fin n) R)) = (n : WithBot ℕ∞) :=
  ⟨fun Q _ => p.isMaximalCohenMacaulay_localization_fiber_mvPolynomial (Fin n) Q,
    p.equidimensional_primeSpectrum_fiber_mvPolynomial (Fin n), by
      simpa using p.ringKrullDim_fiber_mvPolynomial (Fin n)⟩

end Ideal

end
