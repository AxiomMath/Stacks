module

public import StacksFrontier.RingTheory.Module.SurjectivityLocus

@[expose] public section

/-!
# The open locus where a map of modules becomes an isomorphism

Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules with `M` finite and `N`
finitely presented. The set of primes `p` of `R` at which the localized map `φ_p : M_p → N_p` is
bijective is open in `Spec(R)`.

## Main results

* `Stacks.FinitePresentation.BijectiveLocus.solution` and
  `LinearMap.isOpen_setOf_localizedMap_atPrime_bijective`: for `φ : M →ₗ[R] N` with `M` finite
  and `N` finitely presented, the set of primes `p` at which the localized map
  `φ_p : M_p → N_p` is bijective is open in `Spec(R)`.

## Implementation notes

"`φ_p` is an isomorphism" is `Function.Bijective` of the `Localization.AtPrime p`-linear map
`LocalizedModule.map p.asIdeal.primeCompl φ`, the concrete model of the localization of `φ` at `p`
that Mathlib uses for loci of primes (`Module.mem_freeLocus`, `Module.mem_support_iff`).

## References

* [StacksProject 05GF](https://stacks.math.columbia.edu/tag/05GF)

## Tags

isomorphism locus, localization, finitely presented module, Zariski topology
-/

@[expose] public section

namespace Stacks.FinitePresentation.BijectiveLocus

/-- Let `S ≤ T` be submonoids of `R` and let `φ : M →ₗ[R] N`. Localizing `φ_S : M_S → N_S` at `T`
along the natural maps `M_S → M_T` and `N_S → N_T` gives `φ_T : M_T → N_T`. -/
private lemma map_liftOfLE_map {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {S T : Submonoid R} (hST : S ≤ T)
    (φ : M →ₗ[R] N) :
    IsLocalizedModule.map T (LocalizedModule.liftOfLE S T hST (M := M))
        (LocalizedModule.liftOfLE S T hST (M := N))
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S N) φ)
      = IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
        (LocalizedModule.mkLinearMap T N) φ := by
  refine IsLocalizedModule.linearMap_ext T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T N) (LinearMap.ext fun x ↦ ?_)
  conv_lhs => rw [LinearMap.comp_apply,
    show LocalizedModule.mkLinearMap T M x
      = LocalizedModule.liftOfLE S T hST (LocalizedModule.mkLinearMap S M x) from
      (IsLocalizedModule.liftOfLE_apply ..).symm]
  rw [IsLocalizedModule.map_apply, IsLocalizedModule.map_apply, LinearMap.comp_apply,
    IsLocalizedModule.map_apply, IsLocalizedModule.liftOfLE_apply]

/-- If the localization of `φ : M →ₗ[R] N` at a submonoid `S` of `R` is bijective, then so is its
localization at any larger submonoid `T`. -/
private lemma map_bijective_of_le {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {S T : Submonoid R} (hST : S ≤ T)
    (φ : M →ₗ[R] N) (h : Function.Bijective (LocalizedModule.map S φ)) :
    Function.Bijective (LocalizedModule.map T φ) := by
  have hφ : Function.Bijective (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) φ) :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr h
  refine (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N)).mp ?_
  rw [← map_liftOfLE_map hST φ]
  exact ⟨IsLocalizedModule.map_injective T _ _ _ hφ.1,
    IsLocalizedModule.map_surjective T _ _ _ hφ.2⟩

/-- Let `φ : M →ₗ[R] N` be a map of `R`-modules with `M` finite and `N` finitely presented. Then
the set of primes `p` of `R` at which the localized map `φ_p : M_p → N_p` is bijective is open in
`Spec(R)`. -/
public theorem solution
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) [Module.Finite R M] [Module.FinitePresentation R N] :
    IsOpen {p : PrimeSpectrum R |
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ)} := by
  refine isOpen_iff_forall_mem_open.mpr fun p hp ↦ ?_
  obtain ⟨g, hg, hbij⟩ := Module.FinitePresentation.exists_notMem_bijective φ p.asIdeal
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
    ((IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr hp)
  exact ⟨PrimeSpectrum.basicOpen g, fun q hq ↦ map_bijective_of_le
    (Submonoid.powers_le.mpr ((PrimeSpectrum.mem_basicOpen g q).mp hq)) φ hbij,
    (PrimeSpectrum.basicOpen g).2, (PrimeSpectrum.mem_basicOpen g p).mpr hg⟩

end Stacks.FinitePresentation.BijectiveLocus

end

@[expose] public section

/-- Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules with `M` a finite
`R`-module and `N` a finitely presented `R`-module. Then the set of primes `p` of `R` such that
the localized map `φ_p : M_p → N_p` is an isomorphism is an open subset of `Spec(R)`. -/
@[stacks 05GF]
public theorem LinearMap.isOpen_setOf_localizedMap_atPrime_bijective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) [Module.Finite R M] [Module.FinitePresentation R N] :
    IsOpen {p : PrimeSpectrum R |
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ)} :=
  Stacks.FinitePresentation.BijectiveLocus.solution φ

end
