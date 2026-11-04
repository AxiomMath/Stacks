module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence

/-!
# The colength of a localized quotient

Let `B` be a commutative ring, `K` an ideal of `B` and `p` a prime of `B`. There are two ways to
write the local contribution of `B ⧸ K` at `p`: as the localization
`LocalizedModule p.primeCompl (B ⧸ K)` of the module `B ⧸ K`, or as the quotient
`B_p ⧸ K·B_p` of the localized ring. This file records that the two have the same length over
`B_p`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.length_localizedModule_quotient_eq_length_map`:
  the two local colengths agree.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_localizedModule_quotient_eq_length_map_base`:
  the same comparison, with the length taken over a base ring acting through `B` rather than over
  `B_p`.

## Implementation notes

The proof is the standard identification of the localization of a quotient with the quotient of
the localization: `Submodule.toLocalizedQuotient'` is a localization map, so
`IsLocalizedModule.linearEquiv` compares it with the formal localization map, and
`LinearEquiv.extendScalarsOfIsLocalization` upgrades that `B`-linear comparison to a
`B_p`-linear one. The localized submodule is identified with `Ideal.map` by
`Submodule.localized'_eq_span`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- The quotient `B_p ⧸ K·B_p` is `B`-linearly equivalent to the localization of `B ⧸ K` at `p`. -/
private theorem nonempty_linearEquiv_quotient_map_localizedModule {B : Type u} [CommRing B]
    (K : Ideal B) (p : Ideal B) [p.IsPrime] :
    Nonempty ((Localization.AtPrime p ⧸ Ideal.map (algebraMap B (Localization.AtPrime p)) K) ≃ₗ[B]
      LocalizedModule p.primeCompl (B ⧸ K)) := by
  have hloc : (K : Submodule B B).localized' (Localization.AtPrime p) p.primeCompl
        (Algebra.linearMap B (Localization.AtPrime p)) =
      Ideal.map (algebraMap B (Localization.AtPrime p)) K := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  have e : (Localization.AtPrime p ⧸ (K : Submodule B B).localized' (Localization.AtPrime p)
        p.primeCompl (Algebra.linearMap B (Localization.AtPrime p))) ≃ₗ[B]
      LocalizedModule p.primeCompl (B ⧸ K) :=
    IsLocalizedModule.linearEquiv p.primeCompl
      ((K : Submodule B B).toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
        (Algebra.linearMap B (Localization.AtPrime p)))
      (LocalizedModule.mkLinearMap p.primeCompl (B ⧸ K))
  rw [hloc] at e
  exact ⟨e⟩

/-- **The localization of a quotient and the quotient of a localization have the same length.**
For an ideal `K` of `B` and a prime `p`, the `B_p`-length of
`LocalizedModule p.primeCompl (B ⧸ K)` is the `B_p`-length of `B_p ⧸ K·B_p`. -/
public theorem length_localizedModule_quotient_eq_length_map {B : Type u} [CommRing B]
    (K : Ideal B) (p : Ideal B) [p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (B ⧸ K)) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.map (algebraMap B (Localization.AtPrime p)) K) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_quotient_map_localizedModule K p
  rw [← (e.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)).length_eq]

/-- **The localization of a quotient and the quotient of a localization have the same length over
a base ring.** For an ideal `K` of a `R`-algebra `B` and a prime `p` of `B`, the `R`-length of
`LocalizedModule p.primeCompl (B ⧸ K)` is the `R`-length of `B_p ⧸ K·B_p`. -/
public theorem length_localizedModule_quotient_eq_length_map_base {R B : Type u} [CommRing R]
    [CommRing B] [Algebra R B] (K : Ideal B) (p : Ideal B) [p.IsPrime] :
    Module.length R (LocalizedModule p.primeCompl (B ⧸ K)) =
      Module.length R (Localization.AtPrime p ⧸
        Ideal.map (algebraMap B (Localization.AtPrime p)) K) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_quotient_map_localizedModule K p
  rw [← (e.restrictScalars R).length_eq]

end Stacks.ResolutionOfSurfaces.CartierDescent

end
