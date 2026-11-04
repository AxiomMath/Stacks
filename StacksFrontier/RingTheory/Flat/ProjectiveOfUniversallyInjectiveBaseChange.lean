module

public import StacksFrontier.Algebra.MittagLeffler.UniversallyInjectiveProjective
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveBaseChangeFlat
public import StacksFrontier.RingTheory.Module.CountablyGeneratedFiniteType

/-!
# Projectivity of a flat module whose relative associated primes lift to a flat base change

Let `R → S` be a ring map of finite presentation, let `N` be a finitely presented `S`-module which
is flat over `R`, and let `S → S'` be a flat `S`-algebra. Suppose every associated prime of each
fibre of `N` lifts to `S'`. Then `N` is projective over `R` as soon as `N ⊗_S S'` is.

This is the ring-theoretic core of the hard direction of Tag 05MD. In that tag `S'` is the ring of
an étale chart `X' → X` whose image contains the relative assassin of `ℱ`, so that the hypothesis
on associated primes holds and projectivity of `N ⊗_S S'` is supplied by Tag 05KW; the conclusion
is the projectivity of `Γ(X, ℱ)` over `Γ(S, 𝒪_S)` that makes the direct image locally projective.

The three inputs are Tag 05DH, which turns the hypothesis on associated primes into universal
injectivity of `N → N ⊗_S S'` over `R`; the countable generation of `N` over `R`, which comes from
`R → S` being of finite type and `N` being finite over `S`; and the combination of Tags 059N and
059X, which makes a countably generated flat module universally injecting into a projective module
projective.

## Main results

* `Stacks.UniversalInjectivity.projective_of_baseChange_of_flat`: the statement above.

## Implementation notes

The binder list is that of `Stacks.UniversalInjectivity.universallyInjective_baseChange_of_flat`
verbatim, so that the two statements are about the same situation and the same spelling of the
base-change map `N → N ⊗_S S'`, namely `((TensorProduct.mk S N S').flip 1).restrictScalars R`. The
instances `Module R (N ⊗[S] S')` and `IsScalarTower R S (N ⊗[S] S')` that this term needs are the
ones already found for Tag 05DH.

Two hypotheses are added to that list: `Small.{w} R`, the side condition of Tags 059R, 059X and
hence of the Mittag-Leffler step, which is automatic when the ring and the modules live in one
universe; and projectivity of `N ⊗[S] S'` over `R`, which is what the chart supplies.

Flatness of `N` over `R` is carried rather than derived. It is a hypothesis of Tag 05DH already,
and Tag 05MD assumes it of the module, so nothing is gained by routing it through the descent of
flatness along a universally injective map.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.UniversalInjectivity

/-- **Projectivity descends along a flat base change absorbing the relative associated primes.**
Let `R → S` be of finite presentation, let `N` be a finitely presented `S`-module flat over `R`,
and let `S'` be a flat `S`-algebra such that every associated prime of a fibre of `N` is the
contraction of a prime of `S'`. If `N ⊗_S S'` is projective over `R`, then so is `N`.

Tag 05DH makes `N → N ⊗_S S'` universally injective over `R`;
`Module.countablyGenerated_of_finiteType_of_finite` makes `N` countably generated over `R`; and
`Module.projective_of_forall_rTensor_injective_of_countablyGenerated`, which is Tags 059N and
059X, concludes. -/
theorem projective_of_baseChange_of_flat
    {R : Type u} {S : Type v} {S' N : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup N] [Module S N] [Algebra R S] [Algebra S S']
    [Module R N] [IsScalarTower R S N] [Algebra R S'] [IsScalarTower R S S']
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N]
    [Module.Flat R N] [Module.Flat S S']
    [Small.{w} R] [Module.Projective R (N ⊗[S] S')]
    (himage : ∀ (q : Ideal S) [q.IsPrime],
      IsAssociatedPrimeStacks S (N ⊗[R] (q.under R).ResidueField) q →
        ∃ q' : Ideal S', q'.IsPrime ∧ q'.under S = q) :
    Module.Projective R N :=
  Module.projective_of_forall_rTensor_injective_of_countablyGenerated R N (N ⊗[S] S')
    (((TensorProduct.mk S N S').flip 1).restrictScalars R)
    (universallyInjective_baseChange_of_flat himage)
    (Module.countablyGenerated_of_finiteType_of_finite R S N)

end Stacks.UniversalInjectivity

end
