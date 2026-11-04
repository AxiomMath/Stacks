module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Depth of a local ring whose completion has a one-dimensional associated prime

A one-dimensional associated component of the completion of a Noetherian local ring bounds the
depth of the ring itself by one. Equivalently, a Noetherian local ring of depth at least two has
no associated prime `𝔭` of its completion with `dim(Â/𝔭) ≤ 1`.

The second half of the file is the nonfiniteness that the sketch of [Stacks, Tag 0AWC] turns on:
the fraction field of a one-dimensional quotient `B/𝔭` is not a finite `B`-module, and an
associated prime of `B` in the Stacks sense embeds `B/𝔭` into `B`.

## Main results

* `Stacks.LocalCohomology.depth_le_one_of_isAssociatedPrimeStacks_adicCompletion`: if the
  completion `Â` of a Noetherian local ring `A` at its maximal ideal has an associated prime
  `𝔭` with `dim(Â/𝔭) = 1`, then `depth(A) ≤ 1`.
* `Stacks.LocalCohomology.not_two_le_depth_of_isAssociatedPrimeStacks_adicCompletion`: the same
  statement read as the failure of `2 ≤ depth(A)`.
* `Stacks.LocalCohomology.isField_of_module_finite_isFractionRing`: a domain whose fraction
  field is a finite module over it is a field.
* `Stacks.LocalCohomology.not_module_finite_of_ringKrullDim_eq_one`: hence the fraction field of
  a one-dimensional domain is not a finite module over it.
* `Stacks.LocalCohomology.not_module_finite_of_ringKrullDim_quotient_eq_one` and
  `Stacks.LocalCohomology.not_module_finite_of_injective_of_ringKrullDim_quotient_eq_one`: the
  same for the fraction field of `B/𝔭` over `B`, and for any module into which it injects.
* `Stacks.LocalCohomology.exists_injective_quotient_of_isAssociatedPrimeStacks`: an associated
  prime `𝔭` of `B` in the Stacks sense comes with an injection `B/𝔭 ↪ B`.

## Implementation notes

Associated primes are taken in the Stacks Project's sense, as annihilators of single elements
(`IsAssociatedPrimeStacks`); the bridge to Mathlib's `associatedPrimes` is the only translation
step, after which the bound is [Stacks, Tag 0BK4] applied to `Â` as a module over itself,
together with the invariance of depth under completion at the maximal ideal, [Stacks, Tag 07NW].

### Relation to [Stacks, Tag 0AWC]

[Stacks, Tag 0AWC] asserts, for an open immersion `j : U ⟶ X` of integral Noetherian schemes and
a point `z ∈ X ∖ U` whose completed local ring `𝒪^∧_{X,z}` has an associated prime `𝔭` with
`dim(𝒪^∧_{X,z}/𝔭) = 1`, that `j_*𝒪_U` is *not* coherent. This is the converse of
[Stacks, Tag 0BK1], which gives coherence when every associated prime of every such completion
has quotient of dimension at least two, and it is one half of the equivalence of
[Stacks, Tag 0BK3].

The converse of the Hartogs isomorphism
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two` of [Stacks, Tag 0E9I] fails:
coherence of `j_*𝒪_U` does not force `2 ≤ depth(𝒪_{X,z})` at a point `z` outside `U`. For `A`
Noetherian local with punctured spectrum `V`, coherence of the direct image along `V ⟶ Spec(A)`
says that `Γ(V, 𝒪_V)` is a finite `A`-module, equivalently that `H¹_𝔪(A)` is; whereas
`2 ≤ depth(A)` says that `H¹_𝔪(A)` *vanishes*. The two differ: the affine cone over a rational
quartic curve in `P³` is a two-dimensional Noetherian local domain of depth one whose `H¹_𝔪` has
finite length, so there `X = Spec(A)` and `U = V` are integral and Noetherian, `j_*𝒪_V` is
coherent, and `depth(A) = 1`. That example has no associated prime of `Â` with one-dimensional
quotient, so it does not contradict Tag 0AWC — but it does mean that
`not_two_le_depth_of_isAssociatedPrimeStacks_adicCompletion`, true as it is, cannot be combined
with any such converse to prove Tag 0AWC.

The proof of Tag 0AWC uses nonfiniteness instead. Over the completion `B = 𝒪^∧_{X,z}` the
associated prime `𝔭` gives `B/𝔭 ↪ B`
(`exists_injective_quotient_of_isAssociatedPrimeStacks`), `Spec(B/𝔭)` is the two-point space of
the sketch because `B/𝔭` is a one-dimensional local domain, and the sections of `𝒪_{V(𝔭)}` over
the punctured spectrum are `Frac(B/𝔭)`, which is not a finite `B`-module
(`not_module_finite_of_ringKrullDim_quotient_eq_one`) — this is the source's "cannot be finite as
`x` is not a closed point".

## References

* [Stacks Project, Tag 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
* [Stacks Project, Tag 07NW](https://stacks.math.columbia.edu/tag/07NW)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.LocalCohomology

/-- An associated prime in the Stacks sense, for a commutative ring viewed as a module over
itself, is an associated prime in Mathlib's sense. -/
public theorem mem_associatedPrimes_of_isAssociatedPrimeStacks {R : Type*} [CommRing R]
    {p : Ideal R} (hp : IsAssociatedPrimeStacks R R p) : p ∈ associatedPrimes R R := by
  obtain ⟨hprime, m, hm⟩ := hp
  refine ⟨hprime, m, ?_⟩
  have h : Submodule.colon (⊥ : Submodule R R) {m} = p := by simpa using hm
  rw [h, hprime.radical]

/-- If the completion of a Noetherian local ring `A` at its maximal ideal has an associated
prime `𝔭` with `dim(Â/𝔭) = 1`, then `A` has depth at most one.

This is the local-algebra content of the obstruction of [Stacks, Tag 0AWC]: it is
[Stacks, Tag 0BK4] over the completion, transported back along [Stacks, Tag 07NW]. -/
public theorem depth_le_one_of_isAssociatedPrimeStacks_adicCompletion {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    {p : Ideal (AdicCompletion (maximalIdeal A) A)}
    (hp : IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A) p)
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p) = 1) :
    Module.depth A (maximalIdeal A) A ≤ 1 := by
  have hbound := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (mem_associatedPrimes_of_isAssociatedPrimeStacks hp)
  rw [hdim] at hbound
  rw [depth_adicCompletion_maximalIdeal (A := A)]
  exact_mod_cast hbound

/-- A Noetherian local ring of depth at least two has no associated prime of its completion with
one-dimensional quotient. -/
public theorem not_two_le_depth_of_isAssociatedPrimeStacks_adicCompletion {A : Type*}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {p : Ideal (AdicCompletion (maximalIdeal A) A)}
    (hp : IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A) p)
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p) = 1) :
    ¬ 2 ≤ Module.depth A (maximalIdeal A) A := fun h => by
  have h2 : (2 : ℕ∞) ≤ 1 :=
    h.trans (depth_le_one_of_isAssociatedPrimeStacks_adicCompletion hp hdim)
  simp at h2

/-- A domain whose fraction field is a finite module over it is a field: a module-finite
extension is integral, and an integral extension of a domain by a field is a field. -/
public theorem isField_of_module_finite_isFractionRing (C K : Type*) [CommRing C] [IsDomain C]
    [CommRing K] [Algebra C K] [IsFractionRing C K] [Module.Finite C K] : IsField C := by
  let _ : Field K := IsFractionRing.toField C
  exact (Algebra.IsIntegral.isField_iff_isField (IsFractionRing.injective C K)).mpr
    (Field.toIsField K)

/-- The fraction field of a one-dimensional domain is not a finite module over it: were it
finite the domain would be a field, hence of dimension zero. -/
public theorem not_module_finite_of_ringKrullDim_eq_one (C K : Type*) [CommRing C] [IsDomain C]
    [CommRing K] [Algebra C K] [IsFractionRing C K] (hC : ringKrullDim C = 1) :
    ¬ Module.Finite C K := by
  intro hfin
  rw [ringKrullDim_eq_zero_of_isField (isField_of_module_finite_isFractionRing C K)] at hC
  exact absurd hC (by simp)

/-- If `𝔭` is a prime of `B` with `dim(B/𝔭) = 1`, the fraction field of `B/𝔭` is not a finite
`B`-module: a finite `B`-module structure on it restricts to a finite `B/𝔭`-module structure.

Over the completion of a local ring this is the nonfiniteness that the sketch of
[Stacks, Tag 0AWC] turns on: `Frac(B/𝔭)` is the ring of sections of `𝒪_{V(𝔭)}` over the
punctured spectrum, and `V(𝔭)` has only the two points of the sketch. -/
public theorem not_module_finite_of_ringKrullDim_quotient_eq_one {B : Type*} [CommRing B]
    (p : Ideal B) [p.IsPrime] (K : Type*) [CommRing K] [Algebra B K] [Algebra (B ⧸ p) K]
    [IsScalarTower B (B ⧸ p) K] [IsFractionRing (B ⧸ p) K]
    (hp : ringKrullDim (B ⧸ p) = 1) : ¬ Module.Finite B K := fun _ =>
  not_module_finite_of_ringKrullDim_eq_one (B ⧸ p) K hp
    (Module.Finite.of_restrictScalars_finite B (B ⧸ p) K)

/-- Over a Noetherian ring `B`, a module receiving an injection from the fraction field of
`B/𝔭`, for `𝔭` a prime with `dim(B/𝔭) = 1`, is not finite: a submodule of a finite module over
a Noetherian ring is finite. -/
public theorem not_module_finite_of_injective_of_ringKrullDim_quotient_eq_one {B : Type*}
    [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime] (K : Type*) [CommRing K]
    [Algebra B K] [Algebra (B ⧸ p) K] [IsScalarTower B (B ⧸ p) K] [IsFractionRing (B ⧸ p) K]
    (hp : ringKrullDim (B ⧸ p) = 1) {M : Type*} [AddCommGroup M] [Module B M]
    (f : K →ₗ[B] M) (hf : Function.Injective f) : ¬ Module.Finite B M := fun _ =>
  not_module_finite_of_ringKrullDim_quotient_eq_one p K hp (Module.Finite.of_injective f hf)

/-- An associated prime of `B` in the Stacks sense is the annihilator of an element `m`, so
multiplication by `m` embeds `B/𝔭` into `B`.

This is the inclusion `𝒪_{V(𝔭)} ⊆ ℱ` with which the sketch of [Stacks, Tag 0AWC] replaces a
coherent sheaf by the structure sheaf of the closure of an associated point. -/
public theorem exists_injective_quotient_of_isAssociatedPrimeStacks {B : Type*} [CommRing B]
    {p : Ideal B} (hp : IsAssociatedPrimeStacks B B p) :
    ∃ f : (B ⧸ p) →ₗ[B] B, Function.Injective f := by
  obtain ⟨-, m, hm⟩ := hp
  have hker : LinearMap.ker (LinearMap.toSpanSingleton B B m) = p := by
    rw [← hm]
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_colon_singleton, LinearMap.toSpanSingleton_apply]
  refine ⟨Submodule.liftQ p (LinearMap.toSpanSingleton B B m) hker.ge, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le

end Stacks.LocalCohomology

end
