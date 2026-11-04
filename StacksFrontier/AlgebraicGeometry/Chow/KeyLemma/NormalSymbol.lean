module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tame symbol at a height-one prime of a normal domain, and the witnesses for it

The reciprocity relation Stacks 0EAW is a statement about a two-dimensional Noetherian ring
together with a tame symbol on the localization at each of its height-one primes. The symbol is
carried as data — `Stacks.Chow.RegularTameSymbol`, which is how Stacks 0EAH presents it — so the
statement is only as strong as the supply of such data.

This file exhibits that supply in a geometrically relevant class. A height-one localization of a
Noetherian normal domain is a discrete valuation ring, and a discrete valuation ring carries the
tame symbol `Stacks.Chow.dvrRegularTameSymbol`. So over a Noetherian normal domain every
height-one prime has a canonical tame symbol, and the reciprocity summand
`Stacks.Chow.tameSymbolOrderAt` is defined there with no data supplied by hand.

It then checks that the whole hypothesis class is inhabited, and inhabited non-degenerately: the
polynomial ring `k[X₀, X₁]` over a field is a Noetherian normal domain of Krull dimension exactly
two, it has height-one primes, and the finiteness assertion of Stacks 0EAW and the diagonal case
of its vanishing sum hold for it unconditionally, with no hypothesis left to discharge.

## Main definitions

* `Stacks.Chow.normalHeightOneSymbol` — the tame symbol at a height-one prime of a Noetherian
  normal domain.

## Main results

* `Stacks.Chow.isDiscreteValuationRing_localization_of_height_eq_one` — a height-one
  localization of a Noetherian normal domain is a discrete valuation ring.
* `Stacks.Chow.nonempty_heightOnePrime` — a Noetherian domain with a nonzero nonunit has a
  height-one prime.
* `Stacks.Chow.MvPolynomial.ringKrullDim_fin_two`,
  `Stacks.Chow.nonempty_heightOnePrime_mvPolynomial` — `k[X₀, X₁]` is two-dimensional and has
  height-one primes.
* `Stacks.Chow.finite_tameSymbolOrderAt_support_mvPolynomial`,
  `Stacks.Chow.tameSymbolOrderAt_finsum_self_eq_zero_mvPolynomial` — the two assertions of
  Stacks 0EAW that this development proves, instantiated at that ring with its canonical
  symbols and no remaining hypothesis.

## Implementation notes

The uniformizer of the discrete valuation ring is chosen with `Classical.choose`, so
`Stacks.Chow.normalHeightOneSymbol` is noncomputable; the symbol does not depend on that choice
by `Stacks.Chow.dvrRegularTameSymbol_irreducible_congr`.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

/-- **A height-one localization of a Noetherian normal domain is a discrete valuation ring.**
The localization is again Noetherian, local, a domain and integrally closed, and its Krull
dimension is the height of the prime, namely one; a one-dimensional Noetherian normal local
domain is a Dedekind domain, hence a discrete valuation ring. -/
@[ega "II 7.1.6" "special case", sga "3 X 8.9" "partial"]
theorem isDiscreteValuationRing_localization_of_height_eq_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
    exact_mod_cast hp
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime p) := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hz
    exact one_ne_zero hz
  have : Ring.DimensionLEOne (Localization.AtPrime p) := ⟨by
    intro q hq0 hq
    exact (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
      (Ring.krullDimLE_iff.mpr hdim.le)) q hq0 hq⟩
  have : IsDedekindDomain (Localization.AtPrime p) :=
    (isDedekindDomain_iff _ (FractionRing (Localization.AtPrime p))).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing (Localization.AtPrime p))).mp inferInstance⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hnf).out 3 1).mp
    (inferInstance : IsDedekindDomain (Localization.AtPrime p))

/-- **The tame symbol at a height-one prime of a Noetherian normal domain.** The localization is
a discrete valuation ring, and `Stacks.Chow.dvrRegularTameSymbol` is the tame symbol of a
discrete valuation ring; the uniformizer it is built from does not matter, by
`Stacks.Chow.dvrRegularTameSymbol_irreducible_congr`. -/
noncomputable def normalHeightOneSymbol {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (p : HeightOnePrime A) :
    RegularTameSymbol (Localization.AtPrime p.1.asIdeal) :=
  let _ : IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
    isDiscreteValuationRing_localization_of_height_eq_one p.1.asIdeal p.2
  dvrRegularTameSymbol
    (Classical.choose_spec
      (IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p.1.asIdeal)))

/-- **A Noetherian domain with a nonzero nonunit has a height-one prime.** A minimal prime over
the principal ideal the element generates has height at most one by Krull's height theorem, and
is not the zero ideal because it contains the element. -/
theorem nonempty_heightOnePrime {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {x : A} (hx : x ≠ 0) (hx' : ¬ IsUnit x) : Nonempty (HeightOnePrime A) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes
    (I := Ideal.span ({x} : Set A)) (fun h => hx' (Ideal.span_singleton_eq_top.mp h))
  have hpp : p.IsPrime := hp.1.1
  have hxp : x ∈ p := hp.1.2 (Ideal.mem_span_singleton_self x)
  have hne : p ≠ ⊥ := fun he => hx (by simpa using (he ▸ hxp : x ∈ (⊥ : Ideal A)))
  refine ⟨⟨⟨p, hpp⟩, le_antisymm ?_ ?_⟩⟩
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hp
  · exact Order.one_le_iff_ne_zero.mpr fun hz =>
      hne (Ideal.height_eq_zero_iff_eq_bot.mp hz)

section Witness

variable (k : Type u) [Field k]

/-- **The polynomial ring in two variables over a field has Krull dimension two.** This is the
hypothesis `ringKrullDim A = 2` of Stacks 0EAW, exhibited. -/
theorem MvPolynomial.ringKrullDim_fin_two : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
  rw [_root_.MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- A variable is not a unit of the polynomial ring: evaluating at the origin would make `0` a
unit of the base field. -/
theorem not_isUnit_mvPolynomial_X (i : Fin 2) :
    ¬ IsUnit (_root_.MvPolynomial.X i : MvPolynomial (Fin 2) k) := by
  intro hu
  have h := hu.map (_root_.MvPolynomial.eval (fun _ : Fin 2 => (0 : k)))
  rw [_root_.MvPolynomial.eval_X] at h
  exact zero_ne_one (isUnit_zero_iff.mp h)

/-- **The polynomial ring in two variables over a field has height-one primes**, so the index
set of the sum of Stacks 0EAW is not empty there. -/
theorem nonempty_heightOnePrime_mvPolynomial :
    Nonempty (HeightOnePrime (MvPolynomial (Fin 2) k)) :=
  nonempty_heightOnePrime (x := _root_.MvPolynomial.X 0)
    (_root_.MvPolynomial.X_ne_zero 0) (not_isUnit_mvPolynomial_X k 0)

/-- **Stacks 0EAW, finiteness of the sum, with every hypothesis discharged.** For the polynomial
ring in two variables over a field, with the canonical tame symbol at each height-one prime,
only finitely many height-one primes contribute a nonzero order. -/
theorem finite_tameSymbolOrderAt_support_mvPolynomial
    (a b : nonZeroDivisors (MvPolynomial (Fin 2) k)) :
    {p : HeightOnePrime (MvPolynomial (Fin 2) k) |
      tameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p
        (normalHeightOneSymbol p) a b ≠ 0}.Finite :=
  finite_tameSymbolOrderAt_support (MvPolynomial.ringKrullDim_fin_two k)
    normalHeightOneSymbol a b

/-- **The diagonal case of the vanishing sum of Stacks 0EAW, with every hypothesis
discharged.** -/
theorem tameSymbolOrderAt_finsum_self_eq_zero_mvPolynomial
    (a : nonZeroDivisors (MvPolynomial (Fin 2) k)) :
    ∑ᶠ p : HeightOnePrime (MvPolynomial (Fin 2) k),
      tameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p
        (normalHeightOneSymbol p) a a = 0 :=
  tameSymbolOrderAt_finsum_self_eq_zero (MvPolynomial.ringKrullDim_fin_two k)
    normalHeightOneSymbol a

end Witness

end Stacks.Chow

end
