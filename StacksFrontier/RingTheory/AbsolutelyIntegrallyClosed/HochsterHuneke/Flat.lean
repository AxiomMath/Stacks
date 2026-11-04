module

public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.HochsterHuneke.Local
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.HochsterHuneke.FlatnessCriterion
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

@[expose] public section

/-!
# Flatness of the absolute integral closure of a polynomial ring in at most three variables

Let `k` be a field of characteristic `p` and `A = k[x₁, …, x_n]` with `n ≤ 3`. Then an absolute
integral closure `A⁺` of `A` is flat over `A`. This is the case of Hochster and Huneke's theorem
used in the Stacks project to build a flat ring map which is not a filtered colimit of finitely
presented flat ring maps (Stacks, Section 0ATE).

At a prime `Q` of `A` the local ring `A_Q` is a regular local Nagata ring of characteristic `p`
and dimension at most three, and the localization of `A⁺` at `Q` is an absolute integral closure
of `A_Q`; so a regular system of parameters of `A_Q` is a regular sequence on it
(`IsAbsoluteIntegralClosure.isWeaklyRegular_of_ringKrullDim_le_three`). The flatness criterion
`Module.flat_of_forall_isWeaklyRegular_localization` then gives flatness.

## Main results

* `IsAbsoluteIntegralClosure.flat_of_isRegularRing`: over a Noetherian regular Nagata ring of
  characteristic `p` and dimension at most three, an absolute integral closure is flat.
* `MvPolynomial.flat_of_isAbsoluteIntegralClosure`: `k[x₁, …, x_n] → A⁺` is flat for `n ≤ 3`.
* `MvPolynomial.flat_absoluteIntegralClosure`: the same for the absolute integral closure
  constructed in `absoluteIntegralClosure`.

## References

* M. Hochster and C. Huneke, *Infinite integral extensions and big Cohen–Macaulay algebras*,
  Ann. of Math. 135 (1992), 53–89, §6.7.
* [Stacks: Section 0ATE](https://stacks.math.columbia.edu/tag/0ATE)
-/

open IsLocalRing RingTheory.Sequence

universe u

namespace IsAbsoluteIntegralClosure

/-- **Flatness of the absolute integral closure in dimension at most three.** Let `A` be a regular
Nagata domain of characteristic `p` and dimension at most three. Then every absolute integral
closure of `A` is flat over `A`. -/
theorem flat_of_isRegularRing (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsDomain A]
    [IsRegularRing A] [IsNagataRing A] [CharP A p] (hdim : ringKrullDim A ≤ 3) {B : Type u}
    [CommRing B] [IsDomain B] [Algebra A B] (hB : IsAbsoluteIntegralClosure A B) :
    Module.Flat A B := by
  refine Module.flat_of_forall_isWeaklyRegular_localization A B fun Q _ => ?_
  set R := Localization.AtPrime Q
  have : IsRegularLocalRing R := IsRegularRing.isRegularLocalRing_localization Q
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have : IsNagataRing R := isNagata_of_isLocalization A Q.primeCompl R inferInstance
  have hAR : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R Q.primeCompl_le_nonZeroDivisors
  have : CharP R p := charP_of_injective_algebraMap hAR p
  have hdimR : ringKrullDim R ≤ 3 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
  obtain ⟨xs, hxs, hlen⟩ := IsRegularLocalRing.exists_ofList_eq_maximalIdeal_length_eq R
  have hreg : IsRegular R xs :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).1 xs hxs hlen).1
  refine ⟨xs, hxs, hreg, ?_⟩
  -- the localization of `B` at `Q` is an absolute integral closure of `R`
  set B' := Localization (Algebra.algebraMapSubmonoid B Q.primeCompl)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hB.injective
  have hle : Algebra.algebraMapSubmonoid B Q.primeCompl ≤ nonZeroDivisors B :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ Q.primeCompl_le_nonZeroDivisors
  have : IsDomain B' := IsLocalization.isDomain_of_le_nonZeroDivisors B' hle
  have hB' : IsAbsoluteIntegralClosure R B' :=
    hB.localization Q.primeCompl_le_nonZeroDivisors R B'
  have hw : IsWeaklyRegular B' xs :=
    hB'.isWeaklyRegular_of_ringKrullDim_le_three p hdimR hxs hlen
  -- transport along `B_Q ≅ B'`
  have : IsLocalizedModule Q.primeCompl ((Algebra.linearMap B B').restrictScalars A) :=
    IsLocalizedModule.restrictScalars Q.primeCompl (Algebra.linearMap B B')
  let e : LocalizedModule Q.primeCompl B ≃ₗ[R] B' :=
    (IsLocalizedModule.iso Q.primeCompl
      ((Algebra.linearMap B B').restrictScalars A)).extendScalarsOfIsLocalization Q.primeCompl R
  exact (LinearEquiv.isWeaklyRegular_congr e xs).mpr hw

end IsAbsoluteIntegralClosure

namespace MvPolynomial

/-- **Hochster–Huneke for polynomial rings in at most three variables.** Let `k` be a field of
characteristic `p` and `n ≤ 3`. Then every absolute integral closure `B` of `k[x₁, …, x_n]` is flat
over `k[x₁, …, x_n]`. -/
theorem flat_of_isAbsoluteIntegralClosure {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (hn : n ≤ 3) {B : Type u} [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin n) k) B]
    (hB : IsAbsoluteIntegralClosure (MvPolynomial (Fin n) k) B) :
    Module.Flat (MvPolynomial (Fin n) k) B := by
  have hk : ∀ (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S], IsNagataRing S :=
    ((isNagataRing_tfae (R := k)).out 1 2).mp IsNagataRing.of_field
  have : IsNagataRing (MvPolynomial (Fin n) k) := hk _
  refine IsAbsoluteIntegralClosure.flat_of_isRegularRing p ?_ hB
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  exact_mod_cast hn

/-- **Hochster–Huneke for polynomial rings in at most three variables**, for the absolute integral
closure `(k[x₁, …, x_n])⁺` constructed as the integral closure of `k[x₁, …, x_n]` in an algebraic
closure of its fraction field. -/
theorem flat_absoluteIntegralClosure {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (hn : n ≤ 3) :
    Module.Flat (MvPolynomial (Fin n) k) (absoluteIntegralClosure (MvPolynomial (Fin n) k)) :=
  flat_of_isAbsoluteIntegralClosure p hn (isAbsoluteIntegralClosure_absoluteIntegralClosure _)

end MvPolynomial
