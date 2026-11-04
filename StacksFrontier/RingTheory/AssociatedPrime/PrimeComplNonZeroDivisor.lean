module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Flat.AwayReductionInjective

/-!
# Modules whose associated primes all lie under one prime

Let `C` be a Noetherian ring, `M` a `C`-module and `q` a prime of `C`.  Say that `M` is
*concentrated at `q`* if every associated prime of `M` is contained in `q`.  Geometrically this
says that every associated point of the quasi-coherent sheaf attached to `M` specializes to the
point `q`; it is the condition the proof of Stacks 05U7 arranges by shrinking the scheme around
the chosen point.

Two things are proved here.  First, the condition is equivalent to the elementary statement that
no element outside `q` is a zerodivisor on `M`, which is the form in which
`StacksFrontier.RingTheory.Flat.AwayReductionInjective` produces it.  Second — and this is the point
— the condition *persists in every localization of `M`*: for any multiplicative set, and in
particular for the powers of an arbitrary element `a` of `C`, an element outside `q` still acts
injectively on the localized module.  The element `a` is **not** required to lie outside `q`,
which is exactly what makes the statement usable on an arbitrary basic open of `Spec C` rather
than only on the ones containing `q`.

## Main results

* `Module.associatedPrimes_le_of_forall_primeCompl_smul_eq_zero` and
  `Module.forall_primeCompl_smul_eq_zero_of_associatedPrimes_le`: the two readings of the
  condition agree over a Noetherian ring.
* `Module.smul_injective_isLocalizedModule_of_associatedPrimes_le`: an element outside `q` acts
  injectively on any localization of a module concentrated at `q`.
* `Module.smul_injective_localizedModule_powers_of_associatedPrimes_le`: the same for the
  localization away from an arbitrary element.

## Implementation notes

The correspondence between the associated primes of a localization and those of the module is
Mathlib's
`Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`
(Stacks 0310 (3)), which needs the base ring to be Noetherian; the identification of the union of
the associated primes with the set of zerodivisors is Mathlib's
`biUnion_associatedPrimes_eq_zero_divisors`, which needs the same.  No finiteness of `M` is used
anywhere below.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
-/

@[expose] public section

universe u v w

namespace Module

variable {C : Type u} [CommRing C] {M : Type v} [AddCommGroup M] [Module C M]

/-- Over a Noetherian ring, an element is a zerodivisor on `M` iff it lies in an associated
prime. -/
private theorem exists_ne_zero_smul_eq_zero_iff_exists_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] {N : Type*} [AddCommGroup N] [Module R N]
    (r : R) : (∃ x : N, x ≠ 0 ∧ r • x = 0) ↔ ∃ P ∈ associatedPrimes R N, r ∈ P := by
  have := congrArg (r ∈ ·) (biUnion_associatedPrimes_eq_zero_divisors R N)
  simpa using this.symm

/-- If no element outside the prime `q` is a zerodivisor on `M`, then every associated prime of
`M` is contained in `q`. -/
theorem associatedPrimes_le_of_forall_primeCompl_smul_eq_zero [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime]
    (h : ∀ r ∈ q.primeCompl, ∀ m : M, r • m = 0 → m = 0) :
    ∀ P ∈ associatedPrimes C M, P ≤ q := by
  intro P hP x hx
  by_contra hxq
  obtain ⟨m, hm0, hmx⟩ :=
    (exists_ne_zero_smul_eq_zero_iff_exists_mem_associatedPrimes (N := M) x).2 ⟨P, hP, hx⟩
  exact hm0 (h x hxq m hmx)

/-- If every associated prime of `M` is contained in the prime `q`, then no element outside `q`
is a zerodivisor on `M`. -/
theorem forall_primeCompl_smul_eq_zero_of_associatedPrimes_le [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime] (h : ∀ P ∈ associatedPrimes C M, P ≤ q) :
    ∀ r ∈ q.primeCompl, ∀ m : M, r • m = 0 → m = 0 := by
  intro r hr m hm
  by_contra hm0
  obtain ⟨P, hP, hrP⟩ :=
    (exists_ne_zero_smul_eq_zero_iff_exists_mem_associatedPrimes (N := M) r).1 ⟨m, hm0, hm⟩
  exact hr (h P hP hrP)

/-- **An element outside `q` acts injectively on every localization of a module concentrated at
`q`.** Let `C` be Noetherian, let `M` be a `C`-module all of whose associated primes are
contained in the prime `q`, and let `f : M → M'` exhibit `M'` as the localization of `M` at a
multiplicative subset `S`, with `C'` the localization of `C` at `S`.  Then every `r ∉ q` acts
injectively on `M'`.

No relation between `S` and `q` is assumed. -/
theorem smul_injective_isLocalizedModule_of_associatedPrimes_le [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime] (h : ∀ P ∈ associatedPrimes C M, P ≤ q)
    (S : Submonoid C) (C' : Type w) [CommRing C'] [Algebra C C'] [IsLocalization S C']
    {M' : Type*} [AddCommGroup M'] [Module C M'] (f : M →ₗ[C] M') [IsLocalizedModule S f]
    [Module C' M'] [IsScalarTower C C' M']
    {r : C} (hr : r ∈ q.primeCompl) {z : M'} (hz : r • z = 0) : z = 0 := by
  by_contra hz0
  have : IsNoetherianRing C' := IsLocalization.isNoetherianRing S C' inferInstance
  obtain ⟨P, hP, hrP⟩ :=
    (exists_ne_zero_smul_eq_zero_iff_exists_mem_associatedPrimes (N := M') (algebraMap C C' r)).1
      ⟨z, hz0, by rwa [← IsScalarTower.algebraMap_smul C' r z] at hz⟩
  have hcomap : P.comap (algebraMap C C') ∈ associatedPrimes C M := by
    have :=
      associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
        (R := C) (M := M) (M' := M') S C' f
    rw [← this] at hP
    exact hP
  exact hr (h _ hcomap hrP)

/-- **An element outside `q` acts injectively on the localization away from an arbitrary
element.** This is the previous statement for `S = Submonoid.powers a`; the element `a` is
unrestricted, in particular it need not lie outside `q`. -/
theorem smul_injective_localizedModule_powers_of_associatedPrimes_le [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime] (h : ∀ P ∈ associatedPrimes C M, P ≤ q) (a : C)
    {r : C} (hr : r ∈ q.primeCompl)
    {z : LocalizedModule (Submonoid.powers a) M} (hz : r • z = 0) : z = 0 :=
  smul_injective_isLocalizedModule_of_associatedPrimes_le q h (Submonoid.powers a)
    (Localization (Submonoid.powers a)) (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    hr hz

/-- The same conclusion packaged as injectivity of the multiplication map. -/
theorem smul_right_injective_localizedModule_powers_of_associatedPrimes_le [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime] (h : ∀ P ∈ associatedPrimes C M, P ≤ q) (a : C)
    {r : C} (hr : r ∈ q.primeCompl) :
    Function.Injective
      (fun z : LocalizedModule (Submonoid.powers a) M ↦ r • z) := by
  intro z₁ z₂ hz
  have : r • (z₁ - z₂) = 0 := by
    rw [smul_sub]
    simpa [sub_eq_zero] using congrArg (fun t ↦ t) hz
  have := smul_injective_localizedModule_powers_of_associatedPrimes_le q h a hr this
  exact sub_eq_zero.1 this

end Module

/-! ### The same conclusion with no Noetherian hypothesis

For the localization at the powers of an element the statement needs neither associated primes
nor a Noetherian ring: a denominator can simply be absorbed into the element being killed.  The
version below is therefore the one to use; it is stated in the `J • ⊤` form in which the
shrinking step of Stacks 05U7
(`Stacks.AwayReduction.exists_mem_primeCompl_forall_mem_smul_top_localized`) delivers its
hypothesis, and unlike
`Stacks.AwayReduction.forall_mem_smul_top_localized_of_forall_mem_smul_top` it puts **no**
restriction on the element `a` that is inverted.  That is what makes it applicable on an
arbitrary basic open of `Spec C`, not only on the ones containing `q`.
-/

namespace Stacks.AwayReduction

open Submonoid (powers)

variable {C : Type u} [CommRing C] {M : Type v} [AddCommGroup M] [Module C M]

/-- **No element of `q.primeCompl` is a zerodivisor modulo `J` on any away-localization.** If
every `r ∉ q` acts injectively on `M` modulo `J`, then for *every* `a : C` — not only for `a`
outside `q` — every `r ∉ q` acts injectively on `M_a` modulo `J`. -/
theorem forall_mem_smul_top_localized_of_forall_mem_smul_top_of_any
    (J : Ideal C) (q : Ideal C) [q.IsPrime]
    (h : ∀ r ∈ q.primeCompl, ∀ m : M,
      r • m ∈ J • (⊤ : Submodule C M) → m ∈ J • (⊤ : Submodule C M))
    (a : C) :
    ∀ r ∈ q.primeCompl, ∀ ζ : LocalizedModule (powers a) M,
      r • ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers a) M)) →
        ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers a) M)) := by
  intro r hr ζ hζ
  induction ζ using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨m₀, t₀, hmk, hm₀⟩ := exists_mk_of_mem_smul_top (g := a) J hζ
    rw [LocalizedModule.smul'_mk] at hmk
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hmk
    simp only [Submonoid.smul_def] at hu
    have hkey : r • (((u : C) * (t₀ : C)) • m) ∈ J • (⊤ : Submodule C M) := by
      have hcomm : r • (((u : C) * (t₀ : C)) • m) = (u : C) • ((t₀ : C) • (r • m)) := by
        rw [mul_smul, smul_comm r (u : C), smul_comm r (t₀ : C)]
      rw [hcomm, hu]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hm₀)
    have hmem : ((u : C) * (t₀ : C)) • m ∈ J • (⊤ : Submodule C M) := h r hr _ hkey
    have hmk2 : LocalizedModule.mk m t
        = LocalizedModule.mk (((u : C) * (t₀ : C)) • m) (u * t₀ * t) := by
      symm
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul]
      conv_rhs => rw [mul_smul]
      exact smul_comm _ _ _
    rw [hmk2]
    exact mk_mem_smul_top (g := a) J _ hmem

end Stacks.AwayReduction

end
