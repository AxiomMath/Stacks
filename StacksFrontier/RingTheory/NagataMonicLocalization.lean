module

public import StacksFrontier.RingTheory.NagataInfiniteDimension
public import StacksFrontier.RingTheory.Polynomial.MonicLocalization

/-!
# `N⟨X⟩` for Nagata's ring `N`

Let `N` be Nagata's Noetherian ring of infinite dimension (`NagataRing k`) and
`D = N⟨X⟩ = N[X]` localized at the monic polynomials (`Polynomial.MonicLocalization`). Then `D`
is a Noetherian domain of infinite Krull dimension, and it is universally catenary.

## Main results

* `NagataRing.ringKrullDim_monicLocalization_eq_top`: `dim D = ⊤`.
* `NagataRing.exists_field_essFiniteType_monicLocalization`: every local ring of `D` is
  essentially of finite type over a field.
* `NagataRing.isUniversallyCatenary_monicLocalization`: `D` is universally catenary.

That `D` is a Noetherian domain is the instances `Polynomial.isNoetherianRing_monicLocalization`
and `Polynomial.isDomain_monicLocalization`.

## Implementation notes

`dim D ≥ dim N = ⊤` because `𝔭 ↦ 𝔭 N[X]` sends the primes of `N` strictly monotonically to primes
containing no monic polynomial. Universal catenarity: `D` is essentially of finite type over `N`,
each local ring of `N` is essentially of finite type over a field, hence so is each local ring
of `D`, and such a ring is universally catenary.
-/

@[expose] public noncomputable section

universe u

open Polynomial

namespace NagataRing

variable (k : Type u) [Field k]

/-- **`N⟨X⟩` has infinite Krull dimension.** -/
theorem ringKrullDim_monicLocalization_eq_top :
    ringKrullDim (MonicLocalization (NagataRing k)) = ⊤ :=
  top_le_iff.mp (ringKrullDim_eq_top (k := k) ▸
    ringKrullDim_le_of_isLocalization_monicSubmonoid (NagataRing k) _)

/-- Every local ring of `N⟨X⟩` is essentially of finite type over a field. -/
theorem exists_field_essFiniteType_monicLocalization
    (Q : Ideal (MonicLocalization (NagataRing k))) [Q.IsPrime] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra K (Localization.AtPrime Q)),
      Algebra.EssFiniteType K (Localization.AtPrime Q) :=
  Algebra.EssFiniteType.exists_field_essFiniteType_localization (R := NagataRing k)
    (fun P _ => exists_field_essFiniteType P) Q

/-- **`N⟨X⟩` is universally catenary.** -/
theorem isUniversallyCatenary_monicLocalization :
    Ring.IsUniversallyCatenary (MonicLocalization (NagataRing k)) :=
  Ring.IsUniversallyCatenary.of_forall_essFiniteType_field fun Q _ =>
    exists_field_essFiniteType_monicLocalization k Q

end NagataRing
