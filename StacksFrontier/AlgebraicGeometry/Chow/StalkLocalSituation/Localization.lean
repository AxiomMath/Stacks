module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded

/-!
# Absence of embedded associated primes, and full support, pass to a localization

Let `R` be a commutative ring, `S ⊆ R` a submonoid, `R'` a localization of `R` at `S`, and let
`f : M → M'` exhibit `M'` as the localization of an `R`-module `M` at `S`. This file records
that two conditions on `(R, M)` are inherited by `(R', M')`:

* having no embedded associated primes, and
* having full support, i.e. `Supp M = Spec R`.

These are two of the four side conditions of the length formula of
[Stacks, Tag 02QH] (`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient`),
and a localization is how that formula is reached from an affine chart: the local ring of a
scheme at a point of an affine open is a localization of the ring of functions on that open,
and the stalk of a quasi-coherent module there is the corresponding localization of its
sections.

## Main results

* `Stacks.Chow.StalkLocalSituation.hasNoEmbeddedAssociatedPrimes_of_isLocalizedModule`:
  over a Noetherian ring, absence of embedded associated primes passes to a localization.
* `Stacks.Chow.StalkLocalSituation.mem_support_of_comap_mem_support`: a prime of `R'` lies in
  the support of `M'` as soon as its contraction lies in the support of `M`. Together with
  `Module.support_subset_preimage_comap` this says that the support of a localization is the
  preimage of the support.
* `Stacks.Chow.StalkLocalSituation.support_eq_univ_of_isLocalizedModule`: full support passes
  to a localization.

## Implementation notes

The first result is the Noetherian half of Stacks 0310 — Mathlib's
`Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`,
which identifies `Ass(M')` with the primes of `R'` whose contraction is in `Ass(M)` — together
with the injectivity of contraction on the ideals of a localization
(`IsLocalization.map_under`). No finiteness of `M` is needed.

The second result is proved by hand rather than from an annihilator computation, so that it
needs no finiteness hypothesis either: a witness `m` for `p = P ∩ R` in the sense of
`Module.mem_support_iff'` is carried to the witness `f m` for `P`, using that the elements of
`S` become units, hence lie outside `P`, and that `f m = 0` only after multiplication by an
element of `S`.

## References

* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
* [Stacks Project, Tag 00L1](https://stacks.math.columbia.edu/tag/00L1)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public section

namespace Stacks.Chow.StalkLocalSituation

variable {R : Type*} [CommRing R] (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
  [IsLocalization S R']
variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f] [Module R' M'] [IsScalarTower R R' M']

/-! ### Embedded associated primes -/

include S f in
/-- **Absence of embedded associated primes passes to a localization.** Over a Noetherian ring
the associated primes of a localization `M'` of `M` are exactly the primes of `R'` whose
contraction to `R` is associated to `M` (Stacks 0310), and contraction is injective on the
ideals of a localization, so an inclusion between associated primes of `M'` is an inclusion
between associated primes of `M` and therefore an equality. -/
theorem hasNoEmbeddedAssociatedPrimes_of_isLocalizedModule [IsNoetherianRing R]
    (hM : HasNoEmbeddedAssociatedPrimes R M) : HasNoEmbeddedAssociatedPrimes R' M' := by
  have key : (Ideal.comap (algebraMap R R')) ⁻¹' (associatedPrimes R M) = associatedPrimes R' M' :=
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      S R' f
  intro p hp q hq hqp
  have hcomap : Ideal.comap (algebraMap R R') q = Ideal.comap (algebraMap R R') p :=
    hM (key.ge hp) (key.ge hq) (Ideal.comap_mono hqp)
  have hmap := congrArg (Ideal.map (algebraMap R R')) hcomap
  rwa [IsLocalization.map_under S R' q, IsLocalization.map_under S R' p] at hmap

/-! ### Support -/

/-- The image of an element of `S` in a localization does not lie in any prime ideal. -/
private theorem algebraMap_notMem_of_mem {P : Ideal R'} (hP : P.IsPrime) (s : S) :
    algebraMap R R' (s : R) ∉ P := fun hs =>
  hP.ne_top (P.eq_top_of_isUnit_mem hs (IsLocalization.map_units R' s))

include S f in
/-- **A prime of a localization lies in the support of the localized module as soon as its
contraction lies in the support of the module.** The reverse inclusion is
`Module.support_subset_preimage_comap`. -/
theorem mem_support_of_comap_mem_support {P : PrimeSpectrum R'}
    (h : PrimeSpectrum.comap (algebraMap R R') P ∈ Module.support R M) :
    P ∈ Module.support R' M' := by
  rw [Module.mem_support_iff'] at h ⊢
  obtain ⟨m, hm⟩ := h
  refine ⟨f m, fun r' hr' hzero => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
  -- `s` becomes a unit, hence does not lie in the prime `P`.
  have hsP := algebraMap_notMem_of_mem S P.isPrime s
  -- `a` does not lie in `P` either, since `mk' a s * s = a`.
  have haP : algebraMap R R' a ∉ P.asIdeal := by
    intro ha
    rw [← IsLocalization.mk'_spec R' a s] at ha
    exact hr' ((P.isPrime.mul_mem_iff_mem_or_mem.mp ha).resolve_right hsP)
  -- Clearing the denominator in `mk' a s • f m = 0` gives `f (a • m) = 0`.
  have hzero' : f ((a : R) • m) = 0 := by
    have hs := congrArg (fun z : M' => algebraMap R R' (s : R) • z) hzero
    simp only [smul_zero, smul_smul, IsLocalization.mk'_spec'] at hs
    rw [algebraMap_smul] at hs
    rw [f.map_smul]
    exact hs
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S f).mp hzero'
  -- `t * a` is outside the contraction of `P`, contradicting the choice of `m`.
  refine hm ((t : R) * a) (fun hmem => ?_) ?_
  · rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_mul] at hmem
    exact (P.isPrime.mul_mem_iff_mem_or_mem.mp hmem).elim
      (algebraMap_notMem_of_mem S P.isPrime t) haP
  · rwa [mul_smul]

include S f in
/-- **Full support passes to a localization.** Every prime of the localization contracts to a
prime of the base, which lies in the support by hypothesis. -/
theorem support_eq_univ_of_isLocalizedModule (hM : Module.support R M = Set.univ) :
    Module.support R' M' = Set.univ :=
  Set.eq_univ_of_forall fun _ =>
    mem_support_of_comap_mem_support S f (hM ▸ Set.mem_univ _)

end Stacks.Chow.StalkLocalSituation

end
