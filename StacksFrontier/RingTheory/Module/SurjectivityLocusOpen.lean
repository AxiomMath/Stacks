module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import StacksFrontier.RingTheory.Module.SurjectivityLocus

/-!
# The surjectivity locus of a map of modules is open

Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules with `N` a finite `R`-module.
The set `U` of primes `p` at which `φ_p : M_p → N_p` is surjective is the set of primes at which
`φ ⊗ κ(p)` is surjective, `U` is open in `Spec R`, and for every `f : R` with `D(f) ⊆ U` the map
`M_f → N_f` is surjective.

The set `U` is the complement of the support of the cokernel `Q = N ⧸ φ(M)`; as `Q` is finite its
support is closed (`Module.isClosed_support`), and `Q_f = 0` as soon as `D(f)` misses the support
of `Q` (`LocalizedModule.subsingleton_iff_disjoint`).

## Main results

* `LinearMap.setOf_localizedMap_atPrime_surjective_eq_compl_support`: `U` is the complement of the
  support of the cokernel.
* `LinearMap.surjectivityLocus_eq_and_isOpen_and_surjective_away`: Stacks 05GE in full.

## References

* [StacksProject 05GE](https://stacks.math.columbia.edu/tag/05GE)

## Tags

surjective locus, support, open subset, localization
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The set of primes at which the localization of `φ` is surjective is the complement of the
support of the cokernel of `φ`. -/
theorem setOf_localizedMap_atPrime_surjective_eq_compl_support (φ : M →ₗ[R] N) :
    {p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} =
      (Module.support R (N ⧸ φ.range))ᶜ := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
    localizedMap_surjective_iff_subsingleton_localized_coker, Module.notMem_support_iff]

/-- If the cokernel of `φ` is finite, the set of primes at which the localization of `φ` is
surjective is open. -/
theorem isOpen_setOf_localizedMap_atPrime_surjective (φ : M →ₗ[R] N)
    [Module.Finite R (N ⧸ φ.range)] :
    IsOpen {p : PrimeSpectrum R |
      Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} := by
  rw [setOf_localizedMap_atPrime_surjective_eq_compl_support]
  exact Module.isClosed_support.isOpen_compl

/-- If `φ_p` is surjective for every prime `p` of `D(f)`, then `φ_f : M_f → N_f` is surjective. -/
theorem localizedMap_away_surjective_of_basicOpen_subset (φ : M →ₗ[R] N) {f : R}
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
      {p | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)}) :
    Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ) := by
  rw [localizedMap_surjective_iff_subsingleton_localized_coker]
  refine LocalizedModule.subsingleton_iff_disjoint.mpr ?_
  rw [setOf_localizedMap_atPrime_surjective_eq_compl_support] at hf
  exact Set.subset_compl_iff_disjoint_right.mp hf

/-- Let `R` be a ring and let `φ : M →ₗ[R] N` be a map of `R`-modules with `N` a finite
`R`-module. Let `U` be the set of primes `p` such that `φ_p : M_p → N_p` is surjective. Then `U`
is the set of primes `p` such that `φ ⊗ κ(p) : M ⊗_R κ(p) → N ⊗_R κ(p)` is surjective, `U` is open
in `Spec R`, and for every `f : R` with `D(f) ⊆ U` the map `M_f → N_f` is surjective. -/
@[stacks 05GE]
theorem surjectivityLocus_eq_and_isOpen_and_surjective_away (φ : M →ₗ[R] N)
    [Module.Finite R N] :
    {p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} =
        {p | Function.Surjective (φ.baseChange p.asIdeal.ResidueField)} ∧
      IsOpen {p : PrimeSpectrum R |
        Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} ∧
      ∀ f : R, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
          {p | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)} →
        Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ) :=
  ⟨setOf_localizedMap_atPrime_surjective_eq_setOf_baseChange_surjective φ,
    isOpen_setOf_localizedMap_atPrime_surjective φ,
    fun _ hf ↦ localizedMap_away_surjective_of_basicOpen_subset φ hf⟩

end LinearMap

end
