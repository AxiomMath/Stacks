module

public import StacksFrontier.RingTheory.Blowup.Defs

@[expose] public section

/-!
# Dominance of a ring map with power-torsion kernel

Let `f : R →+* S` be a ring map and let `a : R` be an element lying in no minimal prime of `R`.
If every element of the kernel of `f` is annihilated by a power of `a`, then
`Spec S → Spec R` has dense image.

The proof is the source's. A ring map has dense image on spectra exactly when its kernel is
contained in the nilradical, and the nilradical is the intersection of the minimal primes. So
let `x` be in the kernel and let `p` be a minimal prime. Some power `aⁿ` annihilates `x`, hence
`aⁿ x = 0 ∈ p`; as `p` is prime and `a ∉ p`, also `aⁿ ∉ p`, and therefore `x ∈ p`. Thus `x` lies
in every minimal prime, i.e. `x` is nilpotent.

## Main results

* `Stacks.Blowup.PowerTorsionDominance.solution` : Stacks 052T, as stated in
  `PrimeSpectrum.denseRange_comap_of_notMem_minimalPrimes`.

## Implementation notes

The nilpotence step is the whole content of the tag, and is isolated as
`isNilpotent_of_mul_eq_zero_of_notMem_minimalPrimes`, stated for a single multiplication
`a * x = 0`: the power in the source's `aᵏ x = 0` is irrelevant to that argument, and the
`Ideal.sInf_minimalPrimes` bookkeeping is the same either way. It is the minimal-primes
counterpart of Mathlib's `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`, and would be at home
beside it.

The form the Stacks statement uses is its `pow` variant
`isNilpotent_of_pow_mul_eq_zero_of_notMem_minimalPrimes`, whose only content is that lying in no
minimal prime passes from `a` to `aⁿ`, by primality. Splitting the two keeps the reduction of the
statement to the nilradical criterion free of any reasoning about primes.

## References

* [StackProject 052T](https://stacks.math.columbia.edu/tag/052T)
-/

namespace Stacks.Blowup.PowerTorsionDominance

/-- An element annihilated by an element lying in no minimal prime is nilpotent.

This is the form of Stacks 00E0 used by Stacks 052T: `x` lies in every minimal prime `p`, because
`a * x = 0 ∈ p` while `a ∉ p`, and the intersection of the minimal primes is the nilradical. -/
private theorem isNilpotent_of_mul_eq_zero_of_notMem_minimalPrimes {R : Type*} [CommSemiring R]
    {a x : R} (h : a * x = 0) (ha : ∀ p ∈ minimalPrimes R, a ∉ p) : IsNilpotent x := by
  have hx : x ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.2 fun {p} hp ↦
    (hp.1.1.mem_or_mem (h ▸ p.zero_mem)).resolve_left (ha p hp)
  rwa [Ideal.sInf_minimalPrimes] at hx

/-- An element annihilated by a power of an element lying in no minimal prime is nilpotent:
the power lies in no minimal prime either, since the minimal primes are prime. -/
private theorem isNilpotent_of_pow_mul_eq_zero_of_notMem_minimalPrimes {R : Type*}
    [CommSemiring R] {a x : R} {n : ℕ} (h : a ^ n * x = 0)
    (ha : ∀ p ∈ minimalPrimes R, a ∉ p) : IsNilpotent x :=
  isNilpotent_of_mul_eq_zero_of_notMem_minimalPrimes h
    fun p hp hmem ↦ ha p hp (hp.1.1.mem_of_pow_mem n hmem)

public theorem solution {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (a : R)
    (hker : ∀ x : R, f x = 0 → ∃ n : ℕ, a ^ n * x = 0)
    (ha : ∀ p ∈ minimalPrimes R, a ∉ p) :
    DenseRange (PrimeSpectrum.comap f) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  obtain ⟨n, hn⟩ := hker x hx
  exact isNilpotent_of_pow_mul_eq_zero_of_notMem_minimalPrimes hn ha

end Stacks.Blowup.PowerTorsionDominance

/-!
# Blowing up is dominant along an element in no minimal prime

Let `R` be a ring, let `I ⊆ R` be an ideal and let `a ∈ I`. If `a` is contained in no minimal
prime of `R`, then `Spec (R[I/a]) → Spec R` has dense image, where `R[I/a]` is the affine blowup
algebra of `(R, I)` at `a`.

The ideal `I` enters this statement only through the ring `R[I/a]`, and the only property of
`R[I/a]` the mathematics uses is the description of the kernel of the structure map: an element
`x ∈ R` becomes zero in `R[I/a]` exactly when `aⁿ x = 0` for some `n`, because `x/a⁰ = 0/a⁰`
holds iff `aⁿ(a⁰x - a⁰·0) = 0` for some `n`. The general fact behind the tag is therefore:
a ring map `f` whose kernel consists of `a`-power torsion elements has dense image on spectra as
soon as `a` lies in no minimal prime. Such an `x` lies in every minimal prime `p` (as `aⁿ x = 0 ∈ p`
and `a ∉ p`), hence is nilpotent, and a ring map has dense image on spectra iff its kernel is
contained in the nilradical. Both the general lemma and the blowup statement the tag asks for are
recorded here, the latter deduced from the former.

## Main results

* `PrimeSpectrum.denseRange_comap_of_notMem_minimalPrimes`
* `PrimeSpectrum.denseRange_comap_algebraMap_affineBlowupAlgebra`

## Implementation notes

The general lemma is stated for an arbitrary ring map with `a`-power torsion kernel, at the
`CommSemiring` generality of its Mathlib sibling
`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`. The generality is not decoration: the
source's proof uses `I` and `a ∈ I` nowhere, and a statement carrying them would carry two
hypotheses the conclusion does not see. The tag's own subject, the affine blowup algebra `R[I/a]`
of Tag 052Q, is then the second statement, obtained from the first for
`f = algebraMap R (R[I/a])`, the kernel hypothesis being the description of `R[I/a]` recalled
above; since `R[I/a]` is realized as an `R`-subalgebra of a localization `S` of `R` away from `a`,
that description is `IsLocalization.map_eq_zero_iff` for the submonoid of powers of `a`.

The blowup statement is the tagged form of the source's assertion and carries the whole content of
the tag, so it is stated here rather than left to a call site; its derivation from the general
lemma is the kernel computation above and is recorded with it, the general lemma being the only
open obligation.

The blowup statement omits the source's hypothesis `a ∈ I`, which its proof does not use: as
recorded with Tag 052Q, `affineBlowupAlgebra I a S` is the affine blowup algebra of `I + (a)` at
`a` for arbitrary `a`, and `a ∈ I + (a)` always, so nothing is gained by assuming `a ∈ I` and the
statement without it covers strictly more pairs `(I, a)`.

Faithfulness against the source:
* Both hypotheses of the general lemma are used, and neither can be dropped. Without `hker`:
  `R = k[x, y]`, `f : R → R/(y)`, `a = x` lies in the only minimal prime's complement, yet the
  image of the spectrum map is `V(y)`. Without `ha`: `R = k[x, y]/(xy)`, `f : R → R/(y)`, `a = x`
  annihilates the kernel `(y)` but lies in the minimal prime `(x)`, and again the image is `V(y)`.
* The base is the source's: `a` is an element of `R` and the minimal primes are those of `R`, the
  ring the spectrum map lands in.
* The canonical map is pinned: both conclusions are about `PrimeSpectrum.comap` of a given ring
  map, not about the existence of some dominant map.
* The instantiation is not degenerate: for `R = ℤ[x, y]`, `I = (x, y)`, `a = x`, the ring `R` is a
  domain and `a ≠ 0`, so `a` lies in no minimal prime and `R[I/a]` is the affine chart
  `ℤ[x, y, y']/(x y' - y)` of the blowup of the affine plane at the origin.

## References

* [StackProject 052T](https://stacks.math.columbia.edu/tag/052T)
-/

namespace PrimeSpectrum

/-- **Blowing up is dominant.** Let `f : R →+* S` be a ring map and `a : R` an element such that
every element of the kernel of `f` is annihilated by a power of `a`. If `a` is contained in no
minimal prime of `R`, then `Spec S → Spec R` has dense image.

Applied to the affine blowup algebra `S = R[I/a]` of an ideal `I ∋ a` — whose structure map kills
exactly the `a`-power torsion of `R` — this is Stacks Tag 052T; see
`PrimeSpectrum.denseRange_comap_algebraMap_affineBlowupAlgebra`. -/
@[stacks 052T]
public theorem denseRange_comap_of_notMem_minimalPrimes {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (a : R)
    (hker : ∀ x : R, f x = 0 → ∃ n : ℕ, a ^ n * x = 0)
    (ha : ∀ p ∈ minimalPrimes R, a ∉ p) :
    DenseRange (comap f) := by exact Stacks.Blowup.PowerTorsionDominance.solution (S := S) (R := R)
                                 f a hker ha

/-- **Blowing up is dominant.** Let `R` be a ring, `I ⊆ R` an ideal and `a : R`. If `a` is
contained in no minimal prime of `R`, then `Spec (R[I/a]) → Spec R` has dense image, where
`R[I/a] = affineBlowupAlgebra I a S` is the affine blowup algebra of `(R, I)` at `a`, realized
inside a localization `S` of `R` away from `a`.

The source assumes `a ∈ I`; the statement holds without it, since for arbitrary `a` the algebra
`affineBlowupAlgebra I a S` is the affine blowup algebra of `I + (a)` at `a`. -/
@[stacks 052T]
public theorem denseRange_comap_algebraMap_affineBlowupAlgebra {R : Type*} [CommRing R]
    (I : Ideal R) (a : R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away a S]
    (ha : ∀ p ∈ minimalPrimes R, a ∉ p) :
    DenseRange (comap (algebraMap R (affineBlowupAlgebra I a S))) := by
  refine denseRange_comap_of_notMem_minimalPrimes _ a ?_ ha
  intro x hx
  have hx' : algebraMap R S x = 0 := by
    simpa using congrArg (Subalgebra.val (affineBlowupAlgebra I a S)) hx
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers a)] at hx'
  obtain ⟨⟨-, n, rfl⟩, hn⟩ := hx'
  exact ⟨n, hn⟩

end PrimeSpectrum
