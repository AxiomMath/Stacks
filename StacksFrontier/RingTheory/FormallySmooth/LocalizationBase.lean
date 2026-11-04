module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso

/-!
# Adic formal smoothness of a localization map, read downstairs of a localization of the base

Let `R → R' → S` be a tower in which `R'` is a localization of `R` at a submonoid `M`, and let
`q` be a prime of `S`.  The two contractions of `q` to `R'` and to `R` have the *same*
localization — a localization of a localization is a localization — and the map from it to `S_q`
is the same map.  **So the local homomorphism `R'_{q ∩ R'} → S_q` is adically formally smooth if
and only if `R_{q ∩ R} → S_q` is.**

This is the step of the reduced fibre theorem which reconciles the two integral closures that
appear at a generic point of a fibre.  The solution property of Tag 09EN(2) is a statement about
the integral closure of the *localized* base `A_x` in the finite extension, whereas the
identification of the local rings of the normalized base change and the structure morphism of
`Spec B` speak of the integral closure of `B` itself.  The second is a localization of the first
at the image of the complement of the prime under `x`
(`IsLocalization.integralClosure`), and this file is what lets the formal smoothness cross that
localization.

## Main results

* `RingHom.formallySmoothNAdic_localRingHom_of_isLocalization`: adic formal smoothness of
  `R'_{q ∩ R'} → S_q` gives that of `R_{q ∩ R} → S_q`.

## Implementation notes

The transport is `RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq` with the identity on the
target: only the source changes.  The isomorphism of sources is
`IsLocalization.algEquiv`, available because
`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization` exhibits the localization of
`R'` at `q ∩ R'` as a localization of `R` at `q ∩ R`; and that same instance is what lets the
commuting square be checked on elements of `R`, by `IsLocalization.ringHom_ext`, even though the
map whose source it is was built as a localization of `R'`.

## References

* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public section

universe t u v w

namespace RingHom

/-- **Adic formal smoothness of a localization map survives passage to a localization of the
base.**  Let `R'` be a localization of `R` at a submonoid `M`, let `S` be an `R'`-algebra and let
`q` be a prime of `S`.  If `R'_{q ∩ R'} → S_q` is formally smooth for the maximal-ideal-adic
topology of `S_q`, then so is `R_{q ∩ R} → S_q`.

The two sources are the same local ring: `R'_{q ∩ R'}` is a localization of `R` at `q ∩ R`
because a localization of a localization is one, so the comparison is
`IsLocalization.algEquiv` and the two maps to `S_q` agree on `R`. -/
theorem formallySmoothNAdic_localRingHom_of_isLocalization {R : Type u} {R' : Type v}
    {S : Type w} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    [Algebra R' S] [IsScalarTower R R' S] (M : Submonoid R) [IsLocalization M R']
    (q : Ideal S) [q.IsPrime] :
    letI : (q.comap (algebraMap R' S)).IsPrime := Ideal.IsPrime.comap _
    letI : (q.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
    FormallySmoothNAdic.{t, v, w} (Localization.localRingHom (q.comap (algebraMap R' S)) q
        (algebraMap R' S) rfl) (IsLocalRing.maximalIdeal (Localization.AtPrime q)) →
      FormallySmoothNAdic.{t, u, w} (Localization.localRingHom (q.comap (algebraMap R S)) q
        (algebraMap R S) rfl) (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let hP' : (q.comap (algebraMap R' S)).IsPrime := Ideal.IsPrime.comap _
  let hP : (q.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
  intro h
  -- the contraction of `q ∩ R'` to `R` is `q ∩ R`
  have hpc : ((q.comap (algebraMap R' S)).comap (algebraMap R R')).primeCompl =
      (q.comap (algebraMap R S)).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  -- so the localization of `R'` at `q ∩ R'` is the localization of `R` at `q ∩ R`
  have : IsLocalization (q.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap R' S))) := by
    rw [← hpc]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime (q.comap (algebraMap R' S))) (q.comap (algebraMap R' S))
  set e : Localization.AtPrime (q.comap (algebraMap R S)) ≃ₐ[R]
      Localization.AtPrime (q.comap (algebraMap R' S)) :=
    IsLocalization.algEquiv (q.comap (algebraMap R S)).primeCompl _ _
  refine FormallySmoothNAdic.of_arrowEquiv_of_map_eq e.symm.toRingEquiv (RingEquiv.refl _) ?_
    (Ideal.map_id _) h
  refine IsLocalization.ringHom_ext (S := Localization.AtPrime (q.comap (algebraMap R' S)))
    (q.comap (algebraMap R S)).primeCompl (RingHom.ext fun r => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, e.symm.commutes r, RingEquiv.coe_refl, id_eq]
  rw [IsScalarTower.algebraMap_apply R R' (Localization.AtPrime (q.comap (algebraMap R' S))),
    Localization.localRingHom_to_map, Localization.localRingHom_to_map,
    ← IsScalarTower.algebraMap_apply R R' S]

end RingHom

end
