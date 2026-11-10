module

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! ## Localizing at a non-maximal prime is not a local homomorphism

Stacks tag 0H70. If `R` is a local ring and `𝔭 ⊂ R` is a prime that is *not* the maximal
ideal, then `R → R_𝔭` fails to be a local homomorphism — even though both rings are local.

This is the standard trap in the definition of a local ring map (tag 07BI): being a ring map
between local rings is not enough. Localization inverts everything outside `𝔭`, and since
`𝔭 ⊊ 𝔪_R` there is some `x ∈ 𝔪_R \ 𝔭`; that `x` is a nonunit sent to a unit, which is exactly
what `IsLocalHom` forbids.

Note this is a genuine "for all" statement, not the exhibition of one bad ring: *every*
non-maximal prime of *every* local ring gives a failure.
-/

@[expose] public section

open IsLocalRing

/-- **Stacks 0H70**: for a local ring `R` and a non-maximal prime `𝔭`, the localization map
`R → R_𝔭` is not a local homomorphism.

The witness is any `x ∈ 𝔪_R \ 𝔭`, which exists precisely because `𝔭 ⊊ 𝔪_R`: it becomes a unit
in `R_𝔭`, so a local homomorphism would force it to be a unit already in `R`, contradicting
`x ∈ 𝔪_R`. -/
@[stacks 0H70]
theorem not_isLocalHom_algebraMap_atPrime {R : Type*} [CommRing R] [IsLocalRing R]
    (p : Ideal R) [hp : p.IsPrime] (hne : p ≠ maximalIdeal R) :
    ¬ IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
  intro hloc
  have hlt : p < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hp.ne_top) hne
  obtain ⟨x, hxm, hxp⟩ := IsConcreteLE.exists_of_lt hlt
  have hunit : IsUnit (algebraMap R (Localization.AtPrime p) x) :=
    IsLocalization.map_units _ (⟨x, hxp⟩ : p.primeCompl)
  exact (maximalIdeal.isMaximal R).ne_top
    ((maximalIdeal R).eq_top_of_isUnit_mem hxm (hloc.map_nonunit x hunit))

/-- The hypotheses of `not_isLocalHom_algebraMap_atPrime` are satisfiable, so the statement is
not vacuous: in a local domain that is not a field, `⊥` is a prime other than the maximal
ideal, and localizing there — passing to the fraction field — is not a local homomorphism. -/
theorem not_isLocalHom_algebraMap_atPrime_bot {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : ¬ IsField R) :
    ¬ IsLocalHom (algebraMap R (Localization.AtPrime (⊥ : Ideal R))) :=
  not_isLocalHom_algebraMap_atPrime ⊥
    fun hc => h (isField_iff_maximalIdeal_eq.2 hc.symm)
