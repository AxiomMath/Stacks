module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAfterBaseChange

/-!
# Vanishing on the fibres over a set propagates to its closure

Let `R` be a commutative ring and let `f : M →ₗ[R] N` be a map of `R`-modules whose target is
projective. The set of primes `p` at which the fibre map `f ⊗_R κ(p)` vanishes is closed: it is
the zero locus of the flattening ideal of Stacks 083L. Consequently, if `f ⊗_R κ(t)` vanishes
for every `t` in a subset `T` of `Spec R`, it vanishes at every point of the closure of `T`.

This is the commutative-algebra content of Stacks 0CWB, which the source reduces to exactly
this statement: *"let `u : M → N` be a map of `R`-modules with `N` projective such that
`u_t = 0` for every `t ∈ T`; the ideal `I` of Lemma 77.8.3 maps to zero in `κ(t)` for all
`t ∈ T`, so `T ⊂ V(I)`, and as `s` is in the closure of `T` we get `s ∈ V(I)`, whence
`u_s = 0`."*

## Main results

* `Module.rTensor_residueField_eq_zero_iff_exists_ideal`: the fibrewise vanishing locus of a
  map with projective target is the zero locus of an ideal, hence closed.
* `Module.rTensor_residueField_eq_zero_of_mem_closure`: fibrewise vanishing over a subset of
  `Spec R` propagates to the closure of that subset.

## Implementation notes

The fibre of `f` at a prime `p` is `LinearMap.rTensor p.asIdeal.ResidueField f`, the base change
of `f` along the canonical map `R → κ(p)` to the residue field `Ideal.ResidueField` of the
prime. The quotient `R ⧸ p` would not do: the fraction field of a domain is flat but not
faithfully flat over it, so vanishing after base change to `κ(p)` is strictly weaker than
vanishing after base change to `R ⧸ p`, and it is the former that the source asserts.

The ideal is the one produced by `Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot`, the
development's form of Stacks 083L; the only arithmetic needed of the residue field is that the
kernel of `R → κ(p)` is `p`, which is `Ideal.ker_algebraMap_residueField`.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
-/

@[expose] public section

namespace Module

universe u v w x

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- **The fibrewise vanishing locus of a map with projective target is closed.** If `N` is a
projective `R`-module, there is an ideal `I` of `R` such that the base change of `f : M →ₗ[R] N`
to the residue field `κ(p)` of a prime `p` vanishes exactly when `I ⊆ p`.

This is the flattening ideal of Stacks 083L, read on points of `Spec R`. -/
theorem rTensor_residueField_eq_zero_iff_exists_ideal
    (f : M →ₗ[R] N) (hN : Module.Projective R N) :
    ∃ I : Ideal R, ∀ p : PrimeSpectrum R,
      (LinearMap.rTensor p.asIdeal.ResidueField f = 0 ↔ I ≤ p.asIdeal) := by
  obtain ⟨I, hI⟩ := exists_ideal_rTensor_eq_zero_iff_map_eq_bot f hN
  refine ⟨I, fun p => ?_⟩
  have h := hI p.asIdeal.ResidueField (algebraMap R p.asIdeal.ResidueField)
  rw [show (algebraMap R p.asIdeal.ResidueField).toAlgebra = _ from toAlgebra_algebraMap] at h
  rw [h, Ideal.map_eq_bot_iff_le_ker, Ideal.ker_algebraMap_residueField]

/-- **The commutative-algebra content of Stacks 0CWB.** Let `f : M →ₗ[R] N` be a map of
`R`-modules whose target is projective, let `T` be a subset of `Spec R` and let `s` be a point
of the closure of `T`. If the base change of `f` to the residue field `κ(t)` vanishes for every
`t ∈ T`, then it vanishes at `s`.

No hypothesis on `T` beyond being a subset is needed, and `s` need not belong to `T`: the
vanishing locus is the closed set cut out by the flattening ideal of Stacks 083L, so it
contains the closure of any subset it contains. -/
theorem rTensor_residueField_eq_zero_of_mem_closure
    (f : M →ₗ[R] N) (hN : Module.Projective R N)
    (T : Set (PrimeSpectrum R)) (s : PrimeSpectrum R) (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, LinearMap.rTensor t.asIdeal.ResidueField f = 0) :
    LinearMap.rTensor s.asIdeal.ResidueField f = 0 := by
  obtain ⟨I, hI⟩ := rTensor_residueField_eq_zero_iff_exists_ideal f hN
  have hT' : T ⊆ PrimeSpectrum.zeroLocus (I : Set R) := fun t ht =>
    (PrimeSpectrum.mem_zeroLocus t (I : Set R)).mpr ((hI t).mp (hT t ht))
  exact (hI s).mpr
    ((PrimeSpectrum.mem_zeroLocus s (I : Set R)).mp
      (closure_minimal hT' (PrimeSpectrum.isClosed_zeroLocus _) hs))

/-- **The same, after an open base change of the base ring.** Let `φ : R →+* R'` be a ring map
whose map on prime spectra is open — the case the source needs is `φ` étale. Let
`f : M →ₗ[R'] N` be a map of `R'`-modules with projective target, let `T` be a subset of
`Spec R` and let `s'` be a point of `Spec R'` whose image lies in the closure of `T`. If the
base change of `f` to `κ(t')` vanishes at every point `t'` of `Spec R'` lying over `T`, then it
vanishes at `s'`.

This is the whole of the source's proof of Stacks 0CWB downstream of its geometric reduction:
the point `s'` lies in the closure of the inverse image `T'` of `T` *because `Spec R' → Spec R`
is open*, and then `Module.rTensor_residueField_eq_zero_of_mem_closure` applies over `R'`. -/
theorem rTensor_residueField_eq_zero_of_comap_mem_closure
    {R : Type u} [CommRing R] {R' : Type v} [CommRing R'] (φ : R →+* R')
    (hopen : IsOpenMap (PrimeSpectrum.comap φ))
    {M : Type w} [AddCommGroup M] [Module R' M]
    {N : Type x} [AddCommGroup N] [Module R' N]
    (f : M →ₗ[R'] N) (hN : Module.Projective R' N)
    (T : Set (PrimeSpectrum R)) (s' : PrimeSpectrum R')
    (hs : PrimeSpectrum.comap φ s' ∈ closure T)
    (hT : ∀ t' : PrimeSpectrum R', PrimeSpectrum.comap φ t' ∈ T →
      LinearMap.rTensor t'.asIdeal.ResidueField f = 0) :
    LinearMap.rTensor s'.asIdeal.ResidueField f = 0 :=
  rTensor_residueField_eq_zero_of_mem_closure f hN (PrimeSpectrum.comap φ ⁻¹' T) s'
    (hopen.preimage_closure_subset_closure_preimage hs) hT

end Module

end
