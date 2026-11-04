module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Irreducible components of `Spec R` through a prime and minimal primes of `R_𝔭`
-/

@[expose] public section

namespace PrimeSpectrum

variable (R : Type*) [CommSemiring R] (𝔭 : Ideal R) [hp : 𝔭.IsPrime]
  (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S 𝔭]

/-- The point of `Spec(R)` corresponding to a prime ideal `𝔭`. -/
@[ega "I 1.1.1"]
def pt : PrimeSpectrum R := ⟨𝔭, hp⟩

/-- The set of irreducible closed subsets of `Spec(R)` passing through the point
`pt R 𝔭`. -/
abbrev irreducibleClosedThrough : Set (Set (PrimeSpectrum R)) :=
  { Z | IsClosed Z ∧ IsIrreducible Z ∧ pt R 𝔭 ∈ Z }

/-- The set of irreducible components of `Spec(R)` passing through the point
`pt R 𝔭`. -/
abbrev irreducibleComponentsThrough : Set (Set (PrimeSpectrum R)) :=
  { Z ∈ irreducibleComponents (PrimeSpectrum R) | pt R 𝔭 ∈ Z }

/-- The pairs `(prime of R, ≤ 𝔭)` correspond to irreducible closed subsets of
`Spec(R)` passing through `pt R 𝔭`, by sending `𝔮 ↦ V(𝔮)`. -/
def primesBelowEquivIrreducibleClosedThrough :
    { q : Ideal R // q.IsPrime ∧ q ≤ 𝔭 } ≃ irreducibleClosedThrough R 𝔭 where
  toFun q :=
    ⟨zeroLocus (q.1 : Set R), by
      have hq : q.1.IsPrime := q.2.1
      exact ⟨isClosed_zeroLocus _, (isIrreducible_zeroLocus_iff_of_radical _ hq.isRadical).mpr hq,
        (mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr q.2.2)⟩⟩
  invFun Z :=
    ⟨vanishingIdeal (Z.1 : Set (PrimeSpectrum R)),
      isIrreducible_iff_vanishingIdeal_isPrime.mp Z.2.2.1,
      fun _ hf => (mem_vanishingIdeal _ _).mp hf _ Z.2.2.2⟩
  left_inv q := Subtype.ext <| (vanishingIdeal_zeroLocus_eq_radical q.1).trans
    q.2.1.isRadical.radical
  right_inv Z := Subtype.ext <| (zeroLocus_vanishingIdeal_eq_closure Z.1).trans
    Z.2.1.closure_eq

/-- Part (1): The irreducible closed subsets of `Spec(R)` passing through `𝔭`
correspond to the prime ideals of any localization `S` of `R` at `𝔭`. -/
@[stacks 00ET "(1)"]
def irreducibleClosedThroughEquiv :
    irreducibleClosedThrough R 𝔭 ≃ { q : Ideal S // q.IsPrime } :=
  (primesBelowEquivIrreducibleClosedThrough R 𝔭).symm.trans
    (IsLocalization.AtPrime.orderIsoOfPrime S 𝔭).symm.toEquiv

/-- The minimal primes of `R` contained in `𝔭` correspond to irreducible components
of `Spec(R)` passing through `pt R 𝔭`, by sending `𝔮 ↦ V(𝔮)`. -/
@[ega "I 1.1.14" "(i)"]
def minimalPrimesBelowEquivIrreducibleComponentsThrough :
    { q : Ideal R // q ∈ minimalPrimes R ∧ q ≤ 𝔭 } ≃
      irreducibleComponentsThrough R 𝔭 where
  toFun q :=
    ⟨zeroLocus (q.1 : Set R), by
      have hqprime : q.1.IsPrime := q.2.1.isPrime
      refine ⟨?_, (mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr q.2.2)⟩
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨isClosed_zeroLocus _,
        (isIrreducible_zeroLocus_iff_of_radical _ hqprime.isRadical).mpr hqprime⟩, ?_⟩
      rintro Z ⟨hZclosed, hZirr⟩ hsub
      have hJle : vanishingIdeal Z ≤ q.1 := by
        rw [← hqprime.isRadical.radical, ← vanishingIdeal_zeroLocus_eq_radical]
        exact vanishingIdeal_anti_mono hsub
      rw [← le_antisymm hJle (q.2.1.2 ⟨isIrreducible_iff_vanishingIdeal_isPrime.mp hZirr,
        bot_le⟩ hJle), zeroLocus_vanishingIdeal_eq_closure, hZclosed.closure_eq]⟩
  invFun Z :=
    ⟨vanishingIdeal (Z.1 : Set (PrimeSpectrum R)), by
      have hZcomp : Z.1 ∈ irreducibleComponents (PrimeSpectrum R) := Z.2.1
      have hZclosed : IsClosed (Z.1 : Set (PrimeSpectrum R)) :=
        isClosed_of_mem_irreducibleComponents _ hZcomp
      refine ⟨⟨⟨isIrreducible_iff_vanishingIdeal_isPrime.mp hZcomp.1, bot_le⟩, ?_⟩,
        fun f hf => (mem_vanishingIdeal _ _).mp hf _ Z.2.2⟩
      rintro J ⟨hJpr, -⟩ hJle
      have hsub : (Z.1 : Set (PrimeSpectrum R)) ⊆ zeroLocus (J : Set R) := by
        rw [← hZclosed.closure_eq, ← zeroLocus_vanishingIdeal_eq_closure]
        exact zeroLocus_anti_mono_ideal hJle
      rw [irreducibleComponents_eq_maximals_closed] at hZcomp
      have heq : zeroLocus (J : Set R) = Z.1 := (hZcomp.2 ⟨isClosed_zeroLocus _,
        (isIrreducible_zeroLocus_iff_of_radical _ hJpr.isRadical).mpr hJpr⟩ hsub).antisymm hsub
      rw [← heq, vanishingIdeal_zeroLocus_eq_radical, hJpr.isRadical.radical]⟩
  left_inv q := Subtype.ext <| (vanishingIdeal_zeroLocus_eq_radical q.1).trans
    q.2.1.isPrime.isRadical.radical
  right_inv Z := Subtype.ext <| (zeroLocus_vanishingIdeal_eq_closure Z.1).trans
    (isClosed_of_mem_irreducibleComponents _ Z.2.1).closure_eq

/-- The minimal primes of a localization `S` of `R` at `𝔭` correspond, via
contraction, to the minimal primes of `R` contained in `𝔭`.

The map sends a minimal prime `q` of `S` to `Ideal.under R q`; its inverse sends
`q` to `q.map (algebraMap R S)`. Minimality preservation uses the fact that the
algebra map gives a bijection between primes of `S` and primes of `R` contained
in `𝔭` (cf. `IsLocalization.AtPrime.orderIsoOfPrime`). -/
@[sga "1 IV 2.5" "localization at a prime"]
def minimalPrimesLocalizationEquivMinimalPrimesBelow :
    minimalPrimes S ≃
      { q : Ideal R // q ∈ minimalPrimes R ∧ q ≤ 𝔭 } where
  toFun q :=
    ⟨Ideal.under R q.1, by
      have := IsLocalization.AtPrime.isLocalRing S 𝔭
      have hqprime : q.1.IsPrime := q.2.isPrime
      have hq_under_le : Ideal.under R q.1 ≤ 𝔭 := fun x hx =>
        (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 x).mp
          (IsLocalRing.le_maximalIdeal hqprime.ne_top hx)
      refine ⟨⟨⟨hqprime.comap _, bot_le⟩, ?_⟩, hq_under_le⟩
      rintro J ⟨hJprime, -⟩ hJle
      have hdisj : Disjoint (𝔭.primeCompl : Set R) (J : Set R) :=
        Set.disjoint_left.mpr fun _ hxp hxJ => hxp (hJle.trans hq_under_le hxJ)
      have hJmap_le_q : J.map (algebraMap R S) ≤ q.1 :=
        Ideal.map_le_iff_le_comap.mpr hJle
      rw [← le_antisymm hJmap_le_q (q.2.2 ⟨IsLocalization.isPrime_of_isPrime_disjoint
          𝔭.primeCompl S J hJprime hdisj, bot_le⟩ hJmap_le_q),
        IsLocalization.under_map_of_isPrime_disjoint
          𝔭.primeCompl S hJprime hdisj]⟩
  invFun q :=
    ⟨q.1.map (algebraMap R S), by
      have hqprime : q.1.IsPrime := q.2.1.isPrime
      have hdisj : Disjoint (𝔭.primeCompl : Set R) (q.1 : Set R) :=
        Set.disjoint_left.mpr fun _ hxp hxq => hxp (q.2.2 hxq)
      refine ⟨⟨IsLocalization.isPrime_of_isPrime_disjoint
        𝔭.primeCompl S q.1 hqprime hdisj, bot_le⟩, ?_⟩
      rintro J ⟨hJprime, -⟩ hJle
      have hJunder_le_q : J.under R ≤ q.1 := by
        have hsub : J.under R ≤ (q.1.map (algebraMap R S)).under R :=
          Ideal.comap_mono hJle
        rwa [IsLocalization.under_map_of_isPrime_disjoint
          𝔭.primeCompl S hqprime hdisj] at hsub
      rw [← IsLocalization.map_under 𝔭.primeCompl S J,
        le_antisymm hJunder_le_q (q.2.1.2 ⟨hJprime.comap _, bot_le⟩ hJunder_le_q)]⟩
  left_inv q :=
    Subtype.ext <| IsLocalization.map_under 𝔭.primeCompl S q.1
  right_inv q := Subtype.ext <| IsLocalization.under_map_of_isPrime_disjoint
    𝔭.primeCompl S q.2.1.isPrime
    (Set.disjoint_left.mpr fun _ hxp hxq => hxp (q.2.2 hxq))

/-- Part (2): The irreducible components of `Spec(R)` passing through `𝔭`
correspond to the minimal prime ideals of any localization `S` of `R` at `𝔭`. -/
@[stacks 00ET "(2)", ega "IV 5.1.12" "special case"]
def irreducibleComponentsThroughEquiv :
    irreducibleComponentsThrough R 𝔭 ≃ minimalPrimes S :=
  (minimalPrimesBelowEquivIrreducibleComponentsThrough R 𝔭).symm.trans
    (minimalPrimesLocalizationEquivMinimalPrimesBelow R 𝔭 S).symm

variable {R 𝔭 S}

/-- The prime of `S` attached to an irreducible closed subset `Z` through `𝔭` is the extension
of the vanishing ideal of `Z`. -/
@[simp]
lemma coe_irreducibleClosedThroughEquiv (Z : irreducibleClosedThrough R 𝔭) :
    (irreducibleClosedThroughEquiv R 𝔭 S Z : Ideal S) =
      (vanishingIdeal Z.1).map (algebraMap R S) := rfl

/-- The irreducible closed subset attached to a prime `q` of `S` is the zero locus of its
contraction to `R`. -/
@[simp]
lemma coe_irreducibleClosedThroughEquiv_symm (q : { q : Ideal S // q.IsPrime }) :
    ((irreducibleClosedThroughEquiv R 𝔭 S).symm q : Set (PrimeSpectrum R)) =
      zeroLocus (q.1.under R) := rfl

/-- The minimal prime of `S` attached to an irreducible component `Z` through `𝔭` is the
extension of the vanishing ideal of `Z`. -/
@[simp]
lemma coe_irreducibleComponentsThroughEquiv (Z : irreducibleComponentsThrough R 𝔭) :
    (irreducibleComponentsThroughEquiv R 𝔭 S Z : Ideal S) =
      (vanishingIdeal Z.1).map (algebraMap R S) := rfl

/-- The irreducible component attached to a minimal prime `q` of `S` is the zero locus of its
contraction to `R`. -/
@[simp]
lemma coe_irreducibleComponentsThroughEquiv_symm (q : minimalPrimes S) :
    ((irreducibleComponentsThroughEquiv R 𝔭 S).symm q : Set (PrimeSpectrum R)) =
      zeroLocus (q.1.under R) := rfl

end PrimeSpectrum

end
