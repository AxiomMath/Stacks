module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The ring `R⟨X⟩`

For a commutative ring `R`, the ring `R⟨X⟩` is the localization of the polynomial ring `R[X]` at
the multiplicative set of monic polynomials.

## Main definitions

* `Polynomial.monicSubmonoid R`: the monic polynomials, as a submonoid of `R[X]`.
* `Polynomial.MonicLocalization R`: the ring `R⟨X⟩ = R[X]` localized at the monic polynomials.

## Main results

* `Polynomial.isDomain_monicLocalization`, `Polynomial.isNoetherianRing_monicLocalization`:
  `R⟨X⟩` is a domain, resp. Noetherian, when `R` is.
* `Polynomial.essFiniteType_monicLocalization`: `R⟨X⟩` is essentially of finite type over `R`.
* `Polynomial.disjoint_monicSubmonoid_map_C`: for a prime `𝔭` of `R`, `𝔭 R[X]` contains no monic
  polynomial.
* `Polynomial.ringKrullDim_le_of_isLocalization_monicSubmonoid`: `dim R ≤ dim R⟨X⟩`.
-/

@[expose] public noncomputable section

namespace Polynomial

/-- The monic polynomials over `R`, as a submonoid of `R[X]`. -/
def monicSubmonoid (R : Type*) [CommSemiring R] : Submonoid R[X] where
  carrier := {p | p.Monic}
  mul_mem' := Monic.mul
  one_mem' := monic_one

/-- A polynomial lies in `monicSubmonoid R` if and only if it is monic. -/
@[simp]
theorem mem_monicSubmonoid {R : Type*} [CommSemiring R] {p : R[X]} :
    p ∈ monicSubmonoid R ↔ p.Monic :=
  Iff.rfl

/-- The ring `R⟨X⟩`: the polynomial ring `R[X]` localized at the monic polynomials. -/
abbrev MonicLocalization (R : Type*) [CommRing R] : Type _ :=
  Localization (monicSubmonoid R)

/-- Monic polynomials are non-zero-divisors of `R[X]`. -/
theorem monicSubmonoid_le_nonZeroDivisors (R : Type*) [CommRing R] :
    monicSubmonoid R ≤ nonZeroDivisors R[X] :=
  fun _ hp => Monic.mem_nonZeroDivisors hp

/-- `R⟨X⟩` is a domain when `R` is. -/
instance isDomain_monicLocalization (R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (MonicLocalization R) :=
  IsLocalization.isDomain_localization (monicSubmonoid_le_nonZeroDivisors R)

/-- `R⟨X⟩` is Noetherian when `R` is. -/
instance isNoetherianRing_monicLocalization (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (MonicLocalization R) :=
  IsLocalization.isNoetherianRing (monicSubmonoid R) _ inferInstance

/-- `R⟨X⟩` is essentially of finite type over `R`. -/
instance essFiniteType_monicLocalization (R : Type*) [CommRing R] :
    Algebra.EssFiniteType R (MonicLocalization R) :=
  have : Algebra.EssFiniteType R[X] (MonicLocalization R) :=
    .of_isLocalization _ (monicSubmonoid R)
  .comp R R[X] _

/-- For a prime `𝔭` of `R`, the ideal `𝔭 R[X]` contains no monic polynomial. -/
theorem disjoint_monicSubmonoid_map_C {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Disjoint (monicSubmonoid R : Set R[X]) (Ideal.map C p) :=
  Set.disjoint_left.mpr fun g hg hgp => ‹p.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr
    ((show g.Monic from hg).coeff_natDegree ▸ Ideal.mem_map_C_iff.mp hgp g.natDegree))

/-- **`dim R ≤ dim R⟨X⟩`.** The Krull dimension of `R` is at most that of any localization `D` of
`R[X]` at the monic polynomials. -/
theorem ringKrullDim_le_of_isLocalization_monicSubmonoid (R : Type*) [CommRing R] (D : Type*)
    [CommRing D] [Algebra R[X] D] [IsLocalization (monicSubmonoid R) D] :
    ringKrullDim R ≤ ringKrullDim D := by
  let f : PrimeSpectrum R → {q : PrimeSpectrum R[X] //
      Disjoint (monicSubmonoid R : Set R[X]) q.asIdeal} := fun p =>
    ⟨⟨Ideal.map C p.asIdeal, inferInstance⟩, disjoint_monicSubmonoid_map_C p.asIdeal⟩
  have hf : StrictMono f := by
    intro p q hpq
    rw [Subtype.mk_lt_mk, ← PrimeSpectrum.asIdeal_lt_asIdeal]
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal, SetLike.lt_iff_le_and_exists] at hpq
    obtain ⟨hle, a, haq, hap⟩ := hpq
    refine SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.map_mono hle, C a,
      Ideal.mem_map_of_mem _ haq, fun h => hap ?_⟩
    simpa using Ideal.mem_map_C_iff.mp h 0
  exact Order.krullDim_le_of_strictMono _
    ((OrderIso.strictMono (IsLocalization.primeSpectrumOrderIso (monicSubmonoid R) D).symm).comp
      hf)

end Polynomial
