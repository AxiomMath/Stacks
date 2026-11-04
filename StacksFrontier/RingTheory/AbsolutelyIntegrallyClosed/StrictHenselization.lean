module

public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.Absolute
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.StrictlyHenselianTarget

/-!
# The strict henselization maps into a local ring of an absolute integral closure

Let `A` be a local domain, let `B` be an absolute integral closure of `A` and let `q ⊆ B` be a
prime lying over the maximal ideal of `A`. The local ring `B_q` is strictly henselian, by
**Stacks 0DCS** in the form `IsAbsoluteIntegralClosure.isStrictlyHenselian_atPrime`, so the
universal property of the strict henselization against a strictly henselian local algebra applies
to it: a strict henselization `R` of `A` admits a local `A`-algebra map `R → B_q`.

This is the first step of the identification of `B_q` with an absolute integral closure of `R`,
which is what the positive-characteristic alternative of **Stacks 0ATF** runs on. The second step
is recorded here as `IsAbsoluteIntegralClosure.atPrime`, which says that `B_q` *is* an absolute
integral closure of any domain mapping into it injectively and integrally: so the identification
is reduced to exactly two statements about the map produced by the first step, namely that it is
injective and that `B_q` is integral over its image. Neither is proved here; see the
implementation notes.

## Main results

* `IsAbsoluteIntegralClosure.exists_algHom_of_isStrictHenselization`: a strict henselization of
  `A` admits a local `A`-algebra map into `B_q`, for `q` a prime of `B` over the maximal ideal of
  `A`.
* `IsAbsoluteIntegralClosure.atPrime`: `B_q` is an absolute integral closure of every domain which
  maps into it injectively and integrally. The one clause of that which is not a hypothesis is
  absolute integral closedness of `B_q`, which is **Stacks 0DCN** for the localization.

## Implementation notes

*What is still missing for the identification.* Write `f : R → B_q` for the map of the first step.
To conclude `IsAbsoluteIntegralClosure R (B_q)` from `IsAbsoluteIntegralClosure.atPrime` one needs

1. `Function.Injective f`, and
2. `Algebra.IsIntegral R (B_q)` along `f`.

Both are theorems about the ind-étale presentation of `R` that nothing here is strong enough to
prove. For (1): the kernel of `f` is a prime of `R` contracting to `(0)` in `A`, and the primes of
`R` over `(0)` are the primes of the generic fibre `R ⊗_A Frac A`, which is ind-étale over a field
and so zero-dimensional; two of its primes are therefore incomparable, and `(0)` is one of them
once `R` is known to be a domain. For (2): an element of `B_q` is `b/s` with `b` integral over `A`
and `s ∈ B ∖ q`, so it suffices that `1/s` be integral over `R`; since `R` is henselian the finite
`R`-algebra `A[s] ⊗_A R` splits as a product of local rings, and in the factor corresponding to
`q` the image of `s` is a unit. Each of these needs machinery about `R` — that it is a domain,
that its generic fibre is zero-dimensional, that finite algebras over it split — which this file
does not have.

*Flatness of `A → B` is not used and is not stated.* For `A` regular of equal characteristic `p`
it is a theorem of Hochster and Huneke resting on big Cohen–Macaulay algebras; it is the third
missing input of the positive-characteristic alternative of Stacks 0ATF and is independent of the
identification this file is a step towards.

## References

* [Stacks Project, Tag 0DCS](https://stacks.math.columbia.edu/tag/0DCS), strict henselianity of
  `B_q`
* [Stacks Project, Tag 0DCN](https://stacks.math.columbia.edu/tag/0DCN), absolute integral
  closedness of a localization
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU), the universal property
  used
* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF), the example this is a
  step towards
* M. Hochster and C. Huneke, *Infinite integral extensions and big Cohen–Macaulay algebras*,
  Ann. of Math. 135 (1992), 53–89, §6.7.
-/

@[expose] public section

open IsLocalRing

open scoped nonZeroDivisors

universe u v

namespace IsAbsoluteIntegralClosure

variable {A : Type u} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]

/-- A local ring of an absolute integral closure of `A` is an absolute integral closure of every
domain mapping into it injectively and integrally.

It is absolutely integrally closed because a localization of an absolutely integrally closed ring
is one (**Stacks 0DCN**), and that property makes no reference to the base; the other two clauses
of `IsAbsoluteIntegralClosure` are the hypotheses. Unlike
`IsAbsoluteIntegralClosure.localization`, which localizes at the image of a submonoid of `A` and
therefore inherits injectivity and integrality from `A → B`, `q` here is an arbitrary prime of `B`
and both must be supplied. -/
theorem atPrime (h : IsAbsoluteIntegralClosure A B) (C : Type*) [CommRing C] [Algebra B C]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    {R : Type*} [CommRing R] [IsDomain R] [Algebra R C]
    (hinj : Function.Injective (algebraMap R C)) (hint : Algebra.IsIntegral R C)
    (hC : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C
      q.primeCompl_le_nonZeroDivisors) :
    IsAbsoluteIntegralClosure R C where
  injective := hinj
  isIntegral := hint
  isAbsolutelyIntegrallyClosed := isAbsolutelyIntegrallyClosed_localization B q.primeCompl C
    h.isAbsolutelyIntegrallyClosed

/-- **A strict henselization of `A` maps into a local ring of an absolute integral closure.**
Let `A` be a local domain, let `B` be an absolute integral closure of `A`, let `q ⊆ B` be a prime
lying over the maximal ideal of `A` and let `C` be the localization of `B` at `q`. Then every
strict henselization `R` of `A` admits a local `A`-algebra map `R → C`.

`C` is henselian local with separably closed residue field by **Stacks 0DCS**
(`IsAbsoluteIntegralClosure.isStrictlyHenselian_atPrime`), and the structure map `A → C` is local
because `q` lies over the maximal ideal of `A`; so
`Stacks.StrictHenselization.IsStrictHenselization.exists_algHom_of_isSepClosed` applies.

The map is not unique: the automorphisms of the separable closure `κ^sep` over the residue field
of `A` permute the local `A`-algebra maps `R → C`, and it is a prescribed map of residue fields
that singles one out — see
`Stacks.StrictHenselization.IsStrictHenselization.existsUnique_algHom`. -/
theorem exists_algHom_of_isStrictHenselization [IsLocalRing A] (h : IsAbsoluteIntegralClosure A B)
    (C : Type*) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime C q]
    (hq : maximalIdeal A = q.comap (algebraMap A B))
    {κsep : Type*} [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
      [IsSepClosure (maximalIdeal A).ResidueField κsep]
    {R : Type v} [CommRing R] [IsLocalRing R] [Algebra A R]
    (hR : Stacks.StrictHenselization.IsStrictHenselization A κsep R) :
    ∃ f : R →ₐ[A] C, IsLocalHom f := by
  have hCloc : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C q
  obtain ⟨hhens, hsep⟩ := h.isStrictlyHenselian_atPrime C q hCloc
  have := hhens
  have : IsLocalHom (algebraMap A C) := by
    refine ((local_hom_TFAE (algebraMap A C)).out 4 1).mp fun a ha => ?_
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A B C,
      IsLocalization.AtPrime.to_map_mem_maximal_iff C q _ hCloc]
    exact Ideal.mem_comap.mp (hq ▸ ha)
  exact hR.exists_algHom_of_isSepClosed C hsep

end IsAbsoluteIntegralClosure

end
