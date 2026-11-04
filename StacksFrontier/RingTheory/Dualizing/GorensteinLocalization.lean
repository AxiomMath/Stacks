module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# Gorensteinness of a Noetherian ring is stable under localization and isomorphism

`Dualizing.IsGorensteinRing` quantifies over the primes of a ring, so neither of the two
stability statements one expects of it is immediate: that a localization `M⁻¹R` of a Gorenstein
ring is Gorenstein, and that a ring isomorphic to a Gorenstein ring is Gorenstein. This file
proves both.

Both proofs have the same shape. A prime `𝔮` of the target ring is matched with a prime `𝔭` of
the source, the local rings at `𝔭` and at `𝔮` are identified by a ring isomorphism, and
Gorensteinness is carried across that isomorphism by
`Dualizing.isGorensteinLocalRing_of_ringEquiv`. For a localization the matching prime is
the contraction `𝔮 ∩ R` and the identification is that localizing `M⁻¹R` at `𝔮` localizes `R` at
`𝔮 ∩ R`; for an isomorphism `e` the matching prime is `e⁻¹ 𝔮` and the identification comes from
`e` carrying the complement of `e⁻¹ 𝔮` onto the complement of `𝔮`.

## Main results

* `Dualizing.isGorensteinRing_of_isLocalization` — any localization of a Gorenstein Noetherian
  ring at a multiplicative subset is Gorenstein.
* `Dualizing.isGorensteinRing_localization` — the same for the canonical model `Localization M`.
* `Dualizing.isGorensteinRing_of_ringEquiv` — Gorensteinness transports along an isomorphism of
  Noetherian rings.

## Implementation notes

Noetherianness of the target is not a hypothesis but a conclusion: it is forced by that of the
source, and so is supplied by a `letI` inside each statement, since `IsGorensteinRing` cannot be
spelled without it. The instances used are `IsLocalization.isNoetherianRing` and
`isNoetherianRing_of_ringEquiv`.

All rings are taken in a single universe, which is no restriction here: the local rings being
compared are `Localization.AtPrime` of rings that already share a universe, so they share it
too. The transport used, `Dualizing.isGorensteinLocalRing_of_ringEquiv`, does not itself ask
for this.

## References

* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **A localization of a Gorenstein ring is Gorenstein.** If `R` is a Noetherian Gorenstein ring
and `S` is a localization of `R` at a multiplicative subset `M`, then `S` is Gorenstein.

A prime `𝔮` of `S` contracts to a prime `𝔮 ∩ R` of `R`, and localizing `S` at `𝔮` is the same as
localizing `R` at `𝔮 ∩ R`; so the local ring of `S` at `𝔮` is isomorphic to a local ring of `R`
that is Gorenstein by hypothesis. -/
public theorem isGorensteinRing_of_isLocalization {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : IsGorensteinRing R) (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] :
    letI : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
    IsGorensteinRing S := by
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  intro q hq
  let : q.IsPrime := hq
  let : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  exact isGorensteinLocalRing_of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap R S)))
      (Localization.AtPrime q)).symm.toRingEquiv
    (hR (q.comap (algebraMap R S)))

/-- **A localization of a Gorenstein ring is Gorenstein**, for the canonical model `Localization M`
of the localization of `R` at a multiplicative subset `M`. -/
public theorem isGorensteinRing_localization {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : IsGorensteinRing R) (M : Submonoid R) : IsGorensteinRing (Localization M) :=
  isGorensteinRing_of_isLocalization hR M (Localization M)

/-- **Gorensteinness transports along an isomorphism of Noetherian rings.** If `R ≃+* S` and `R`
is Gorenstein, then so is `S`.

A prime `𝔮` of `S` pulls back to a prime `e⁻¹ 𝔮` of `R`, and `e` carries the complement of
`e⁻¹ 𝔮` onto the complement of `𝔮`, hence induces an isomorphism of the two local rings; the one
over `R` is Gorenstein by hypothesis. -/
public theorem isGorensteinRing_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (e : R ≃+* S) (hR : IsGorensteinRing R) :
    letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
    IsGorensteinRing S := by
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  intro q hq
  let : q.IsPrime := hq
  exact isGorensteinLocalRing_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap e))
      (Localization.AtPrime q) e (e.map_primeCompl_comap_eq q)).symm
    (hR (q.comap e))

end Dualizing

end
