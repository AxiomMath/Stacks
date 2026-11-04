module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# A zero-dimensional localization at a prime of a ring with prime nilradical

Let `ψ : R → S` exhibit a local ring `S` of Krull dimension zero as the localization of `R` at
the prime `P` lying under the maximal ideal of `S`. If the nilradical of `R` is prime, that is if
`R` has a single minimal prime, then `P` *is* the nilradical: an element of `P` becomes nilpotent
in the zero-dimensional local ring `S`, so some power of it is killed by an element outside `P`,
and that element lies outside the prime nilradical.

So the residue field of `S` depends only on `R`: it is the residue field of `R` at its nilradical.
In particular it is carried along by any ring isomorphism `R ≃+* R'`, which is the form used to
compare the function fields of base changes of two schemes with isomorphic function fields.

## Main results

* `IsLocalization.AtPrime.comap_maximalIdeal_eq_nilradical`: the prime localized at is the
  nilradical.
* `IsLocalization.AtPrime.exists_residueField_ringEquiv_of_ringEquiv`: a ring isomorphism of the
  two rings induces an isomorphism of the residue fields of the two localizations.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Ring.KrullDimLE 0 S]

/-- If a zero-dimensional local ring `S` is the localization of `R` at the prime lying under its
maximal ideal, and the nilradical of `R` is prime, then that prime is the nilradical of `R`. -/
theorem comap_maximalIdeal_eq_nilradical (ψ : R →+* S)
    (hloc : letI := ψ.toAlgebra
      IsLocalization.AtPrime S (Ideal.comap ψ (maximalIdeal S)))
    (hR : (nilradical R).IsPrime) :
    Ideal.comap ψ (maximalIdeal S) = nilradical R := by
  let := ψ.toAlgebra
  refine le_antisymm (fun x hx => ?_) (nilradical_le_prime _)
  obtain ⟨n, hn⟩ := Ring.KrullDimLE.isNilpotent_iff_mem_nonunits.mpr hx
  obtain ⟨⟨t, ht⟩, hts⟩ := (IsLocalization.map_eq_zero_iff
    (Ideal.comap ψ (maximalIdeal S)).primeCompl S _).mp ((map_pow _ x n).trans hn)
  exact hR.mem_of_pow_mem n ((hR.mem_or_mem (hts ▸ zero_mem _)).resolve_left
    fun h => ht (nilradical_le_prime _ h))

variable {R' S' : Type*} [CommRing R'] [CommRing S'] [IsLocalRing S'] [Ring.KrullDimLE 0 S']

/-- Under the hypotheses of `comap_maximalIdeal_eq_nilradical`, `S` is the localization of `R` at
the prime complement of the nilradical. -/
private theorem isLocalization_nilradical_primeCompl (ψ : R →+* S)
    (hloc : letI := ψ.toAlgebra
      IsLocalization.AtPrime S (Ideal.comap ψ (maximalIdeal S)))
    (hR : (nilradical R).IsPrime) :
    letI := ψ.toAlgebra
    IsLocalization (nilradical R).primeCompl S := by
  let := ψ.toAlgebra
  have h : (Ideal.comap ψ (maximalIdeal S)).primeCompl = (nilradical R).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, comap_maximalIdeal_eq_nilradical ψ hloc hR]
  exact h ▸ hloc

/-- Let `ψ : R → S` and `ψ' : R' → S'` exhibit zero-dimensional local rings as localizations at
the primes under their maximal ideals, where the nilradical of `R` is prime. A ring isomorphism
`θ : R ≃+* R'` induces an isomorphism of the residue fields of `S` and `S'` compatible with `ψ`,
`ψ'` and `θ`: both primes are the nilradicals, which `θ` matches. -/
theorem exists_residueField_ringEquiv_of_ringEquiv (ψ : R →+* S) (ψ' : R' →+* S')
    (hloc : letI := ψ.toAlgebra
      IsLocalization.AtPrime S (Ideal.comap ψ (maximalIdeal S)))
    (hloc' : letI := ψ'.toAlgebra
      IsLocalization.AtPrime S' (Ideal.comap ψ' (maximalIdeal S')))
    (hR : (nilradical R).IsPrime) (θ : R ≃+* R') :
    ∃ Φ : ResidueField S ≃+* ResidueField S',
      ∀ r, Φ (residue S (ψ r)) = residue S' (ψ' (θ r)) := by
  let := ψ.toAlgebra
  let := ψ'.toAlgebra
  have hcomap : Ideal.comap θ.symm.toRingHom (nilradical R) = nilradical R' := by
    ext x
    simp only [Ideal.mem_comap, mem_nilradical, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact ⟨fun h => by simpa using h.map θ.toRingHom, fun h => h.map θ.symm.toRingHom⟩
  have hR' : (nilradical R').IsPrime := hcomap ▸ Ideal.comap_isPrime θ.symm.toRingHom _
  have hl := isLocalization_nilradical_primeCompl ψ hloc hR
  have hl' := isLocalization_nilradical_primeCompl ψ' hloc' hR'
  have hM : (nilradical R).primeCompl.map θ.toMonoidHom = (nilradical R').primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, mem_nilradical]
    refine ⟨?_, fun hx => ⟨θ.symm x, fun h => hx (by simpa using h.map θ.toRingHom), by simp⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact fun h => hy (by simpa using h.map θ.symm.toRingHom)
  exact ⟨ResidueField.mapEquiv (IsLocalization.ringEquivOfRingEquiv S S' θ hM), fun r =>
    congrArg (residue S') (IsLocalization.ringEquivOfRingEquiv_eq (S := S) (Q := S') hM r)⟩

end IsLocalization.AtPrime

end
