module

import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ClosedSupportRepresentative
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutLift
public import StacksFrontier.RingTheory.Spectrum.Prime.NonminimalPrimes

/-!
# The image of local cohomology supported in the nonminimal primes

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization and let `T'` be
the subset of primes of `T` that are not minimal in `T`. A class in `Hⁱ_T(K)` comes from
`Hⁱ_{T'}(K)` exactly when it dies after localizing at every prime that is minimal in `T`.

One implication is immediate: a class supported in `T'` localizes to zero at any prime outside
`T'`, in particular at a minimal prime of `T`. For the converse, a class annihilated by an ideal
`D` has a representative `y` with closed support `V(I) ⊆ T` which is again annihilated by `D`.
Only finitely many primes of `V(I)` are minimal in `T`, and the hypothesis provides, for each of
them, an element of `D` outside it; prime avoidance then yields a single `f ∈ D` lying in no such
prime. Cutting `y` by `f` gives a class supported in `V(I) ∩ V(f)`, and that closed set contains
no prime minimal in `T`, hence lies in `T'`.

Dually, a class in `Hⁱ_{T'}(K)` dies in `Hⁱ_T(K)` exactly when it is cut out by a principal
equation: it comes from a class with closed support `V(I) ∩ V(f)`, where `V(I) ⊆ T`, which
already dies on `V(I)`. Here a closed-support representative `V(I₀) ⊆ T'` of the class is
enlarged until it dies, and prime avoidance produces an `f` in `I₀` missing each of the finitely
many primes of `V(I)` minimal in `T`, so that `V(I) ∩ V(f)` avoids them all.

## Main results

* `Stacks.LocalCohomology.range_changeOfSupport_eq_localizationKernel` — the image of
  `Hⁱ_{T'}(K) → Hⁱ_T(K)` is the set of classes whose localizations at the minimal primes of `T`
  vanish.
* `Stacks.LocalCohomology.kernel_changeOfSupport_eq_closedSupportImages` — the kernel of
  `Hⁱ_{T'}(K) → Hⁱ_T(K)` consists of the classes coming from a closed support `V(I) ∩ V(f)`
  with `V(I) ⊆ T` on which they already vanish.

## Implementation notes

These are exactness at `Hⁱ_T(K)` and at `Hⁱ_{T'}(K)` for the sequence of the source. The
exactness at `Hⁱ_{T'}(K)` is recorded through the closed-support representatives of the colimit
term `colim_{Z, f} H¹_f(Hⁱ⁻¹_Z(K))`, rather than through that colimit itself; the colimit, the
injectivity of its map into `Hⁱ_{T'}(K)`, the map to the direct sum `⨁_𝔭 Hⁱ_𝔭(K_𝔭)` over the
minimal primes of `T` and the exactness there are assembled from these two statements in
`StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/NonminimalPrimesColimit.lean` and
`StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/ExactSequence.lean`.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Prime avoidance over a closed support: if `V(I) ⊆ T` and no prime of `V(I)` minimal in `T`
contains `D`, then some `f ∈ D` cuts `V(I)` down into the nonminimal primes of `T`. -/
theorem exists_mem_zeroLocus_inter_subset_nonminimalPrimes {A : Type u} [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (I D : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T)
    (hD : ∀ p ∈ T \ PrimeSpectrum.nonminimalPrimes T, p ∈ PrimeSpectrum.zeroLocus (I : Set A) →
      ¬ (D : Set A) ⊆ p.asIdeal) :
    ∃ f ∈ D, PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) ⊆
      PrimeSpectrum.nonminimalPrimes T := by
  have havoid : ¬ (D : Set A) ⊆ ⋃ P ∈ PrimeSpectrum.asIdeal '' {p : PrimeSpectrum A |
      p ∈ T \ PrimeSpectrum.nonminimalPrimes T ∧ p ∈ PrimeSpectrum.zeroLocus (I : Set A)},
      (P : Set A) := by
    intro hsub
    obtain ⟨P, ⟨p, hp, rfl⟩, hDP⟩ := (Ideal.subset_union_prime_finite
      ((finite_minimalSupportPrimes_in_closedSupport T I hI).image _)
      (f := fun P : Ideal A => P) ⊤ ⊤ (by rintro P ⟨p, hp, rfl⟩ _ _; exact p.isPrime)).mp hsub
    exact hD p hp.1 hp.2 hDP
  obtain ⟨f, hfD, hfavoid⟩ := Set.not_subset.mp havoid
  refine ⟨f, hfD, fun p hp => ?_⟩
  by_contra hpn
  exact hfavoid (Set.mem_iUnion.2 ⟨p.asIdeal, Set.mem_iUnion.2
    ⟨Set.mem_image_of_mem _ ⟨⟨hI hp.1, hpn⟩, hp.1⟩,
      (PrimeSpectrum.mem_zeroLocus p _).1 hp.2 (by simp)⟩⟩)

/-- **Exactness at local cohomology with support in `T`.** Over a Noetherian ring, a class in
`Hⁱ_T(K)` is the image of a class supported in the nonminimal primes of `T` if and only if it
localizes to zero at every prime that is minimal in `T`. -/
@[stacks 0EF8 "exactness at local cohomology with support in T"]
theorem range_changeOfSupport_eq_localizationKernel
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn.{u, v} A T K i) :
    (∃ y : localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i,
      (changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T) K i).hom y = x) ↔
      ∀ p : PrimeSpectrum A, p ∈ T \ PrimeSpectrum.nonminimalPrimes T →
        (ModuleCat.localizedModuleMkLinearMap
          (localCohomologyWithSupportIn.{u, v} A T K i) p.asIdeal.primeCompl) x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ p hp
    rw [localizedModuleMk_natural p.asIdeal.primeCompl
        (changeOfSupport.{u, v} A (PrimeSpectrum.nonminimalPrimes_subset T) K i) y,
      localCohomology_localizes_zero_outside_support.{u, v}
        (PrimeSpectrum.nonminimalPrimes T) K i p hp.2 y, map_zero]
  · intro hx
    obtain ⟨J, y, hy, hyD⟩ := exists_closedSupport_representative_annihilated.{u, v} A T hT K i x
      (LinearMap.ker (LinearMap.toSpanSingleton A _ x)) fun _ ha => ha
    obtain ⟨f, hfD, hadm⟩ := exists_mem_zeroLocus_inter_subset_nonminimalPrimes T
      (OrderDual.ofDual J).1 (LinearMap.ker (LinearMap.toSpanSingleton A _ x))
      (OrderDual.ofDual J).2 fun p hp _ hDP => by
        obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
          (ModuleCat.localizedModuleMkLinearMap _ p.asIdeal.primeCompl)).mp (hx p hp)
        exact a.property (hDP ha)
    obtain ⟨z, hz⟩ :=
      exists_closedSupport_principal_lift.{u, v} A (OrderDual.ofDual J).1 f K i y (hyD f hfD)
    refine ⟨(changeOfSupport A hadm K i).hom z, ?_⟩
    rw [changeOfSupport_trans_apply,
      ← changeOfSupport_trans_apply A Set.inter_subset_left (OrderDual.ofDual J).2, hz, hy]

/-- **Exactness at local cohomology with support in the nonminimal primes.** Over a Noetherian
ring, a class in `Hⁱ_{T'}(K)` dies in `Hⁱ_T(K)` if and only if it is the image of a class with
closed support `V(I) ∩ V(f) ⊆ T'`, where `V(I) ⊆ T`, which already vanishes in
`Hⁱ_{V(I)}(K)`. -/
@[stacks 0EF8 "exactness at local cohomology with support in the nonminimal primes T'"]
theorem kernel_changeOfSupport_eq_closedSupportImages
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i) :
    (changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T) K i).hom x = 0 ↔
      ∃ (I : Ideal A) (f : A) (_hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T)
        (hadm : PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) ⊆
          PrimeSpectrum.nonminimalPrimes T)
        (y : localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A) ∩
          PrimeSpectrum.zeroLocus ({f} : Set A)) K i),
        (changeOfSupport A hadm K i).hom y = x ∧
          (changeOfSupport A Set.inter_subset_left K i).hom y = 0 := by
  constructor
  · intro hx
    obtain ⟨J₀, y₀, hy₀⟩ := exists_closedSupport_representative.{u, v} A
      (PrimeSpectrum.nonminimalPrimes T)
      (PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes hT) K i x
    set I₀ : Ideal A := (OrderDual.ofDual J₀).1
    have hI₀T' : PrimeSpectrum.zeroLocus (I₀ : Set A) ⊆ PrimeSpectrum.nonminimalPrimes T :=
      (OrderDual.ofDual J₀).2
    have hI₀T : PrimeSpectrum.zeroLocus (I₀ : Set A) ⊆ T :=
      hI₀T'.trans (PrimeSpectrum.nonminimalPrimes_subset T)
    have hzeroT : (changeOfSupport.{u, v} A hI₀T K i).hom y₀ = 0 := by
      rw [← changeOfSupport_trans_apply A hI₀T' (PrimeSpectrum.nonminimalPrimes_subset T), hy₀,
        hx]
    obtain ⟨L, hJL, hLzero⟩ := exists_closedSupport_map_eq_zero.{u, v} A T hT K i
      (OrderDual.toDual ⟨I₀, hI₀T⟩) y₀ hzeroT
    set I : Ideal A := (OrderDual.ofDual L).1
    have hIT : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T := (OrderDual.ofDual L).2
    obtain ⟨f, hfI₀, hadm⟩ := exists_mem_zeroLocus_inter_subset_nonminimalPrimes T I I₀ hIT
      fun p hp _ hDP => hp.2 (hI₀T' ((PrimeSpectrum.mem_zeroLocus p _).mpr hDP))
    have hcut : PrimeSpectrum.zeroLocus (I₀ : Set A) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) :=
      fun p hp => ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal hJL hp,
        (PrimeSpectrum.mem_zeroLocus p _).2
          (Set.singleton_subset_iff.mpr ((PrimeSpectrum.mem_zeroLocus p _).1 hp hfI₀))⟩
    exact ⟨I, f, hIT, hadm, (changeOfSupport.{u, v} A hcut K i).hom y₀,
      (changeOfSupport_trans_apply A hcut hadm K i y₀).trans hy₀,
      (changeOfSupport_trans_apply A hcut Set.inter_subset_left K i y₀).trans hLzero⟩
  · rintro ⟨I, f, hI, hadm, y, rfl, hyzero⟩
    rw [changeOfSupport_trans_apply, ← changeOfSupport_trans_apply A
      (Set.inter_subset_left (t := PrimeSpectrum.zeroLocus ({f} : Set A))) hI, hyzero, map_zero]

end Stacks.LocalCohomology

end
