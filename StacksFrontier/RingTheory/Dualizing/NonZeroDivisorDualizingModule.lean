module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Dualizing.AssociatedPrimeRegular
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# A nonzerodivisor of the ring is a nonzerodivisor on a dualizing module

Let `A` be a Noetherian ring and let `M` be an `A`-module whose complex `M[n]` in some
cohomological degree is a dualizing complex ([Stacks, Tag 0A7B]). Then every nonzerodivisor of
`A` acts injectively on `M`.

This is the global form of the statement that the local equation of an effective Cartier divisor
is a nonzerodivisor on a dualizing module. An element that is not injective on `M` lies in an
associated prime `p` of `M` ([Stacks, Tag 00LL]), and the localization `M_p` is again a dualizing
module, now over the local ring `A_p` with its maximal ideal associated
([Stacks, Tag 0310]); over such a ring no element of the maximal ideal is a nonzerodivisor
([Stacks, Tag 0AWS]), while the image of a nonzerodivisor under a flat map still is one.

## Main results

* `Dualizing.isDualizingComplex_single_zero_of_isDualizingComplex_single`: a module whose complex
  in some degree is dualizing has its degree-zero complex dualizing too.
* `Dualizing.isDualizingComplex_single_localizedModule`: the localization at a prime of a
  dualizing module is a dualizing module over the localized ring.
* `Dualizing.isSMulRegular_of_isDualizingComplex_single`: a nonzerodivisor of a Noetherian ring
  is a nonzerodivisor on a dualizing module.

## Implementation notes

The reduction of the degree is the shift isomorphism of the family of single functors: shifting
`M[n]` by `n` gives `M[0]`, and a shift of a dualizing complex is a dualizing complex
(`Dualizing.isDualizingComplex_shift`).

Localizing is [Stacks, Tag 0A7G] in the form
`Dualizing.isDualizingComplex_extendScalars_of_isLocalization`: extension of scalars along
`A → A_p` is exact, so it is the functor induced degreewise on the derived categories, it carries
a degree-zero complex to a degree-zero complex (Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`), and the module it produces is the
canonical localized module.

Universes: `Dualizing.IsNormalizedDualizingComplex`, which the local input
`Dualizing.not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal` goes through, is pinned at
`HasDerivedCategory.standard` and stated for `ModuleCat.{u} A`, so everything below is read at
the module universe of the ring and at the standard model of the derived category.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **A dualizing module in any degree is a dualizing module in degree zero.** Shifting the
complex `M[n]` by `n` produces `M[0]`, and a shift of a dualizing complex is dualizing. -/
theorem isDualizingComplex_single_zero_of_isDualizingComplex_single (M : ModuleCat.{u} A) (n : ℤ)
    (hM : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) :
    IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
  isDualizingComplex_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n 0 n (add_zero n)).app M)
    (isDualizingComplex_shift _ hM n)

/-- **The localization of a dualizing module at a prime is a dualizing module.** This is
[Stacks, Tag 0A7G] for the degree-zero complex on `M`, read at the canonical localized module
`M_p` over `A_p`. -/
theorem isDualizingComplex_single_localizedModule (M : ModuleCat.{u} A)
    (hM : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
    (p : Ideal A) [p.IsPrime] :
    IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M))) := by
  have hflat : (algebraMap A (Localization.AtPrime p)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.AtPrime p) p.primeCompl)
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime p))) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  let : PreservesColimitsOfSize.{u, u}
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime p))) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime p))) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  refine isDualizingComplex_of_iso ?_
    (isDualizingComplex_extendScalars_of_isLocalization p.primeCompl _ hM)
  exact ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Localization.AtPrime p))).mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).mapIso
      (extensionLocalizationIso.{u, u} p.primeCompl M)

/-- **A nonzerodivisor of a Noetherian ring is a nonzerodivisor on a dualizing module.** If the
complex `M[n]` in some cohomological degree is a dualizing complex ([Stacks, Tag 0A7B]), then
every `t` in `nonZeroDivisors A` acts injectively on `M`. -/
theorem isSMulRegular_of_isDualizingComplex_single (M : ModuleCat.{u} A) (n : ℤ)
    (hM : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M))
    (t : A) (ht : t ∈ nonZeroDivisors A) :
    IsSMulRegular M t := by
  by_contra hreg
  -- A zerodivisor on `M` lies in an associated prime of `M`.
  obtain ⟨p, hp, htp⟩ : ∃ p ∈ associatedPrimes A M, t ∈ p := by
    by_contra hcon
    exact hreg ((isSMulRegular_iff_forall_notMem_associatedPrimes t).mpr
      fun q hq htq => hcon ⟨q, hq, htq⟩)
  let : p.IsPrime := hp.1
  -- `M_p` is a dualizing module over `A_p`, and the maximal ideal is one of its associated primes.
  have hdual := isDualizingComplex_single_localizedModule M
    (isDualizingComplex_single_zero_of_isDualizingComplex_single M n hM) p
  have hass : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  -- The image of `t` lies in the maximal ideal of `A_p` and is still a nonzerodivisor there.
  have htmax : algebraMap A (Localization.AtPrime p) t ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p t).mpr htp
  have htreg : IsSMulRegular (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p) t) :=
    IsSMulRegular.of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Module.Flat.isSMulRegular_of_nonZeroDivisors ht)
  exact not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) hdual hass htmax htreg

end Dualizing

end
