module

public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Being a normal domain is invariant under henselization

A normal local domain `R` — a domain integrally closed in its field of fractions — has a
henselization which is again a normal local domain. This is the implication `(1) ⇒ (2)` of
Stacks 06DI, which `isNormalDomain_tfae_henselization_strictHenselization` states for the
henselization and the strict henselization living in the *same* universe as `R`, alongside each
other. The cross-universe uniqueness of henselizations of
`StacksFrontier.RingTheory.Henselian.HenselizationCompletion` transports it to an arbitrary
henselization `H`, exactly as
`StacksFrontier.RingTheory.Henselian.ReducedDimensionOneNoetherianOfHenselization` transports
reducedness, Noetherianity and the dimension.

## Main results

* `StacksDraft.isDomain_and_isIntegrallyClosed_of_isHenselization`: a normal local domain has a
  henselization, in any universe, which is a normal domain.

## Implementation notes

"Normal domain" is `IsDomain` together with `IsIntegrallyClosed`, Mathlib's integral closedness
in `FractionRing`, which for a domain is the field of fractions; this is the spelling of
`isNormalDomain_tfae_henselization_strictHenselization` and of the normal-domain item of
`isDiscreteValuationRing_tfae`, so no translation is needed at either end.

The two conclusions are returned as a conjunction rather than as instances because neither is
available before the henselization is named, and a caller holding the pair can install both with
`let`. The strict henselization that the same-universe statement needs is the one
`IsLocalRing.henselizationTower` supplies over a separable closure of the residue field; it does
not appear in the conclusion.

## References

* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace StacksDraft

/-- **Being a normal domain is invariant under henselization.** If a local ring `R` is a domain
integrally closed in its field of fractions, then so is any henselization `H` of `R`, even one
living in a different universe.

The same-universe statement is Stacks 06DI,
`isNormalDomain_tfae_henselization_strictHenselization`, applied to the henselization and strict
henselization supplied by `IsLocalRing.henselizationTower`, and transported to `H` along the
cross-universe isomorphism `StacksDraft.exists_ringEquiv_of_isHenselization`. -/
@[ega "IV 18.6.9" "(i), special case", ega "IV 7.5.3" "(vi), special case"]
theorem isDomain_and_isIntegrallyClosed_of_isHenselization
    {R : Type u} {H : Type v} [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H] :
    IsDomain H ∧ IsIntegrallyClosed H := by
  let κ := SeparableClosure (ResidueField R)
  let T := henselizationTower R κ
  obtain ⟨e, -⟩ := exists_ringEquiv_of_isHenselization (R := R) (H := H) (H' := T.henselization)
  obtain ⟨_, _⟩ : IsDomain T.henselization ∧ IsIntegrallyClosed T.henselization :=
    ((isNormalDomain_tfae_henselization_strictHenselization R T.henselization
      T.strictHenselization κ).out 1 2).mp
        (⟨inferInstance, inferInstance⟩ : IsDomain R ∧ IsIntegrallyClosed R)
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective,
    IsIntegrallyClosed.of_equiv e.symm⟩

end StacksDraft

end
