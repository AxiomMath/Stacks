module

public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes

/-!
# An ind-étale domain over a domain embeds in every domain it maps to over the base

Let `A` be a domain and let `R` be an ind-étale `A`-algebra which is itself a domain. If `C` is a
domain over `A` on which `A` acts injectively, then every `A`-algebra map `R → C` is injective.

For `R` a strict henselization of a *normal* local domain `A` this is the first of the two
statements that, by `IsAbsoluteIntegralClosure.atPrime`, identify a local ring `(A⁺)_q` of an
absolute integral closure of `A` as an absolute integral closure of `R`; the second, integrality,
is `IsAbsoluteIntegralClosure.isIntegral_atPrime`. The map in question is the one produced by
`IsAbsoluteIntegralClosure.exists_algHom_of_isStrictHenselization`.

## Main results

* `StacksDraft.injective_of_indEtale_of_isDomain`: the injectivity statement above.
* `IsAbsoluteIntegralClosure.injective_atPrime`: its application to `(A⁺)_q`, for `R` any
  ind-étale local domain over `A` — in particular a strict henselization of a normal local
  domain, where `IsDomain R` is **Stacks 06DI**.

## Implementation notes

The kernel `𝔮` of `R → C` is a prime of `R`, because `C` is a domain, and it contracts to `(0)`
in `A`, because `A → C` is injective. An ind-étale algebra is flat
(`CommAlgCat.flat_of_ind_etale`) and all of its fibres are zero-dimensional
(`StacksDraft.fiber_reduced_and_krullDimLE_zero`, which is where ind-étaleness over the field
`κ(p)` is used), so by
`StacksDraft.minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero` the minimal primes of `R` are
exactly the primes over minimal primes of `A`. Both `A` and `R` are domains, so the minimal
primes on either side are just `(0)`; hence `𝔮 = (0)`.

This replaces the sketch recorded in
`StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.StrictHenselization`, which went through
incomparability of the primes of the generic fibre by hand; the minimal-prime correspondence
already in the tree packages the same content.

*`IsDomain R` is a genuine hypothesis, not a derivable one.* It is supplied for a strict
henselization of a normal local domain by Stacks 06DI
(`isNormalDomain_tfae_henselization_strictHenselization`); without normality the strict
henselization of a local domain need not be a domain, and the conclusion fails.

*Flatness of `A → A⁺` is nowhere used.* The flatness used here is that of `A → R`, which is a
consequence of ind-étaleness.

## References

* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI), normality of a strict
  henselization
* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF), the example this is a
  step towards
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace StacksDraft

/-- **An ind-étale domain over a domain maps injectively into any domain over the base on which
the base acts injectively.** Let `A` be a domain, let `R` be an ind-étale `A`-algebra which is a
domain, and let `C` be a domain with `A → C` injective and `A → R → C` a tower. Then `R → C` is
injective.

The kernel is a prime of `R` over `(0)`; the minimal primes of an ind-étale algebra are exactly
the primes over minimal primes of the base
(`minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero`, applicable because an ind-étale algebra is
flat with zero-dimensional fibres), and in two domains those are `(0)` on both sides. -/
theorem injective_of_indEtale_of_isDomain {A : Type u} [CommRing A] [IsDomain A] {R : Type v}
    [CommRing R] [IsDomain R] [Algebra A R] (hind : StacksDraft.IndEtale A R) {C : Type w}
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra R C] [IsScalarTower A R C]
    (hA : Function.Injective (algebraMap A C)) : Function.Injective (algebraMap R C) := by
  have : Module.Flat A R :=
    have : Module.Flat A (ULift.{u} R) := CommAlgCat.flat_of_ind_etale hind
    Module.Flat.of_linearEquiv (ULift.algEquiv : ULift.{u} R ≃ₐ[A] R).symm.toLinearEquiv
  have hdim : ∀ (p : Ideal A) [p.IsPrime], Ring.KrullDimLE 0 (p.Fiber R) := fun p _ =>
    (fiber_reduced_and_krullDimLE_zero hind p).2
  have hker : (RingHom.ker (algebraMap R C)).IsPrime := RingHom.ker_isPrime _
  -- the kernel contracts to `(0)` in `A`, because `A → C` is injective
  have hlo : (RingHom.ker (algebraMap R C)).LiesOver (⊥ : Ideal A) := by
    refine ⟨le_antisymm bot_le fun a ha => ?_⟩
    have : algebraMap A C a = 0 := by
      rw [IsScalarTower.algebraMap_apply A R C]
      exact ha
    simpa using hA (by simpa using this)
  -- so it is a minimal prime of `R`, hence `(0)` since `R` is a domain
  have hmin : RingHom.ker (algebraMap R C) ∈ minimalPrimes R :=
    (minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero hdim _).mpr
      ⟨hker, ⊥, by simp [IsDomain.minimalPrimes_eq_singleton_bot], hlo⟩
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hmin
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hmin

end StacksDraft

namespace IsAbsoluteIntegralClosure

variable {A : Type u} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]

/-- **A local ring of an absolute integral closure receives an ind-étale domain injectively.**
Let `B` be an absolute integral closure of the domain `A`, let `q` be a prime of `B` and let `C`
be the localization of `B` at `q`. If `R` is an ind-étale `A`-algebra which is a domain, mapping
to `C` over `A`, then `R → C` is injective.

`A → C` is injective because `A → B` is (`h.injective`) and the complement of `q` consists of
nonzerodivisors of the domain `B`; `C` is a domain for the same reason. So
`StacksDraft.injective_of_indEtale_of_isDomain` applies.

Together with `IsAbsoluteIntegralClosure.isIntegral_atPrime` this supplies both hypotheses of
`IsAbsoluteIntegralClosure.atPrime`, for `R` a strict henselization of a normal local domain
`A`: ind-étaleness is the `isFilteredColimitEtale` field of
`Stacks.StrictHenselization.IsStrictHenselization`, and `IsDomain R` is **Stacks 06DI**. -/
theorem injective_atPrime (h : IsAbsoluteIntegralClosure A B)
    (C : Type v) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    {R : Type*} [CommRing R] [IsDomain R] [Algebra A R] [Algebra R C] [IsScalarTower A R C]
    (hind : StacksDraft.IndEtale A R) : Function.Injective (algebraMap R C) := by
  have : IsDomain C :=
    IsLocalization.isDomain_of_le_nonZeroDivisors C q.primeCompl_le_nonZeroDivisors
  refine StacksDraft.injective_of_indEtale_of_isDomain hind ?_
  rw [IsScalarTower.algebraMap_eq A B C]
  exact (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp h.injective

end IsAbsoluteIntegralClosure

end
