module

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Associated primes transport along a ring isomorphism

An associated prime of a ring, viewed as a module over itself, pulls back along a ring
isomorphism to an associated prime of the source.

## Main results

* `Stacks.LocalCohomology.associatedPrimeStacks_comap_ringEquiv`: the comap of an associated
  prime along a ring isomorphism is associated.

## Implementation notes

The Stacks Project's definition of an associated prime is that it be the annihilator of a single
element, so transport amounts to checking that the annihilator of the preimage of that element is
the comap of the annihilator; both inclusions follow from injectivity of the isomorphism.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
-/

@[expose] public section

namespace Stacks.LocalCohomology

/-- The preimage of an associated prime of `S` under a ring isomorphism `R ≃+* S` is an
associated prime of `R`. -/
public theorem associatedPrimeStacks_comap_ringEquiv {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) (p : Ideal S)
    (hp : IsAssociatedPrimeStacks S S p) :
    IsAssociatedPrimeStacks R R (Ideal.comap (e : R →+* S) p) := by
  rcases hp with ⟨hprime, a, ha⟩
  have ha' : (⊥ : Ideal S).colon ({a} : Set S) = p := by simpa using ha
  refine ⟨Ideal.comap_isPrime e.toRingHom p, e.symm a, ?_⟩
  have hEq : (⊥ : Ideal R).colon ({e.symm a} : Set R) =
      Ideal.comap (e : R →+* S) p := by
    ext x
    rw [Ideal.mem_comap, ← ha', Submodule.mem_colon_singleton,
      Submodule.mem_colon_singleton]
    simp only [Submodule.mem_bot, smul_eq_mul]
    exact ⟨fun hx => by simpa using congrArg e hx, fun hx => e.injective (by simpa using hx)⟩
  simpa using hEq

end Stacks.LocalCohomology
