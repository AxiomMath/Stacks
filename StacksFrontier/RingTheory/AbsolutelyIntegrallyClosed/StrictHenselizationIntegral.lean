module

public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.StrictHenselizationInjective
public import StacksFrontier.RingTheory.Henselian.IntegralUnitInverse

/-!
# A local ring of an absolute integral closure is integral over a henselian local algebra

Let `A` be a domain, let `B` be an absolute integral closure of `A`, let `q ⊆ B` be a prime and
let `C = B_q`. If `R` is a henselian local `A`-algebra with a local structure map `R → C`, then
`C` is integral over `R`.

This is the second of the two statements that, by
`IsAbsoluteIntegralClosure.atPrime`, identify `C` as an absolute integral closure of a strict
henselization `R` of `A`; the map `R → C` is the one produced by
`IsAbsoluteIntegralClosure.exists_algHom_of_isStrictHenselization`. The first statement,
injectivity, is `IsAbsoluteIntegralClosure.injective_atPrime`, and the two are combined here into
the identification itself.

## Main results

* `IsAbsoluteIntegralClosure.isIntegral_atPrime`: `C` is integral over `R`.
* `IsAbsoluteIntegralClosure.atPrime_of_indEtale`: **the identification.** For `R` an ind-étale
  henselian local domain over `A` mapping locally into `C`, `C` *is* an absolute integral closure
  of `R`.

## Implementation notes

An element of `C` is `b/s` with `b, s ∈ B`, and `b` is integral over `A` hence over `R`, so all
the content is that the inverse of the unit `s` of `C` is integral over `R`. That is exactly
`HenselianLocalRing.isIntegral_val_inv`, which gets it from the henselian splitting of a finite
algebra over `R` in the form "`R[s]` is local": the hypothesis that `R → C` is local is what makes
`s`, a unit of `C`, already a unit of `R[s]`.

Nothing here uses that `R` is a strict henselization, only that it is henselian local and maps
locally into `C`; and nothing uses flatness of `A → B`, which for `A` regular of equal
characteristic `p` is the theorem of Hochster and Huneke and is a separate missing input of the
positive-characteristic alternative of **Stacks 0ATF**.

## References

* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF), the example this is a
  step towards
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG), the henselian splitting
  behind `HenselianLocalRing.isIntegral_val_inv`
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsAbsoluteIntegralClosure

variable {A : Type u} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]

/-- **A local ring of an absolute integral closure is integral over a henselian local algebra
mapping locally into it.** Let `B` be an absolute integral closure of the domain `A`, let `q` be a
prime of `B` and let `C` be the localization of `B` at `q`. If `R` is a henselian local
`A`-algebra with `R → C` a local homomorphism over `A`, then `C` is integral over `R`.

Every element of `C` is `b * s⁻¹` for `b : B` and `s` in the complement of `q`. The image of `b`
is integral over `A`, because `B` is, and hence over `R`; and `s⁻¹` is integral over `R` by
`HenselianLocalRing.isIntegral_val_inv`, applied to the unit of `C` given by `s` — whose value is
integral over `R` for the same reason as `b`. The product of two integral elements is integral.

Applied to the map of `IsAbsoluteIntegralClosure.exists_algHom_of_isStrictHenselization`, whose
source is henselian and whose structure map is local, this supplies the `hint` hypothesis of
`IsAbsoluteIntegralClosure.atPrime`. -/
theorem isIntegral_atPrime (h : IsAbsoluteIntegralClosure A B)
    (C : Type v) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    {R : Type*} [CommRing R] [HenselianLocalRing R] [Algebra A R] [Algebra R C]
    [IsScalarTower A R C] [IsLocalHom (algebraMap R C)] :
    Algebra.IsIntegral R C := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C q
  have : IsDomain C :=
    IsLocalization.isDomain_of_le_nonZeroDivisors C q.primeCompl_le_nonZeroDivisors
  have := h.isIntegral
  -- the image in `C` of an element of `B` is integral over `R`
  have hB : ∀ b : B, IsIntegral R (algebraMap B C b) := fun b =>
    (IsIntegral.map (IsScalarTower.toAlgHom A B C)
      (Algebra.IsIntegral.isIntegral (R := A) b)).tower_top
  refine ⟨fun c => ?_⟩
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj q.primeCompl c
  -- `s` is a unit of `C`; its inverse is integral over `R` by the henselian argument
  obtain ⟨t, ht⟩ := IsLocalization.map_units (M := q.primeCompl) C s
  have hinv : IsIntegral R ((t⁻¹ : Cˣ) : C) :=
    HenselianLocalRing.isIntegral_val_inv t (ht ▸ hB (s : B))
  have hc : c = algebraMap B C b * ((t⁻¹ : Cˣ) : C) := by
    have hb : algebraMap B C b = c * (t : C) := by rw [ht]; exact hbs.symm
    rw [hb, mul_assoc, t.mul_inv, mul_one]
  rw [hc]
  exact (hB b).mul hinv

/-- **A local ring of an absolute integral closure of `A` is an absolute integral closure of an
ind-étale henselian local domain over `A` mapping locally into it.** Let `B` be an absolute
integral closure of the domain `A`, let `q` be a prime of `B` and let `C` be the localization of
`B` at `q`. Let `R` be an `A`-algebra which is a domain, henselian local, ind-étale over `A`, and
whose structure map `R → C` is local over `A`. Then `IsAbsoluteIntegralClosure R C`.

This is `IsAbsoluteIntegralClosure.atPrime` with both of its hypotheses discharged:
`injective_atPrime` gives injectivity and `isIntegral_atPrime` gives integrality.

A strict henselization `R` of a normal local domain `A` satisfies every hypothesis:
`HenselianLocalRing R` and `StacksDraft.IndEtale A R` are the `henselian` and
`isFilteredColimitEtale` fields of `Stacks.StrictHenselization.IsStrictHenselization`, `IsDomain R`
is **Stacks 06DI** (`isNormalDomain_tfae_henselization_strictHenselization`), and the local
structure map over `A` is what
`IsAbsoluteIntegralClosure.exists_algHom_of_isStrictHenselization` produces. That is the
identification the positive-characteristic alternative of **Stacks 0ATF** runs on; what 0ATF still
needs beyond it is flatness of `A → B`, which is the theorem of Hochster and Huneke and is not
stated anywhere in this development. -/
theorem atPrime_of_indEtale (h : IsAbsoluteIntegralClosure A B)
    (C : Type v) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    {R : Type*} [CommRing R] [IsDomain R] [HenselianLocalRing R] [Algebra A R] [Algebra R C]
    [IsScalarTower A R C] [IsLocalHom (algebraMap R C)] (hind : StacksDraft.IndEtale A R)
    (hC : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C
      q.primeCompl_le_nonZeroDivisors) :
    IsAbsoluteIntegralClosure R C :=
  h.atPrime C q (h.injective_atPrime C q hind) (h.isIntegral_atPrime C q) hC

end IsAbsoluteIntegralClosure

end
