module

public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A strict henselization is flat over the ring it henselizes

A strict henselization `S → Sˢʰ` is realized as a filtered colimit of étale `S`-algebras: this
is property (2) of the characterization, recorded as the field
`Stacks.StrictHenselization.IsStrictHenselization.isFilteredColimitEtale`, which says that
`ULift Sˢʰ` satisfies the ind-property of the class of étale `S`-algebras, i.e. that it is the
colimit of a filtered diagram of étale `S`-algebras. A filtered colimit of étale algebras is
flat, so `Sˢʰ` is a flat `S`-module.

## Main results

* `Stacks.StrictHenselization.IsStrictHenselization.flat` — a strict henselization is flat over
  the base.

## Implementation notes

The content is `CommAlgCat.flat_of_ind_etale` (Stacks 00U2 and 05UT): the cocone maps of an
ind-presentation need not be injective, so the étale stages are not subalgebras of `Sˢʰ` and the
flatness of `Sˢʰ` is not a directed union of flat subalgebras; what carries over instead is the
equational criterion, a finite relation in `Sˢʰ` being pushed back into a single étale stage
after moving along one map of the index category.

The field is recorded for `ULift Sˢʰ`, so that the base and the strict henselization may lie in
independent universes; flatness transports back to `Sˢʰ` along `ULift.algEquiv`.

## References

* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
-/

@[expose] public section

open IsLocalRing

universe u w

namespace Stacks.StrictHenselization

/-- **A strict henselization is flat over the base.** Property (2) of a strict henselization
writes it as a filtered colimit of étale `S`-algebras; étale algebras are flat, and a filtered
colimit of flat algebras is flat. -/
@[sga "4 VIII 4.4"]
theorem IsStrictHenselization.flat
    {S : Type u} [CommRing S] [IsLocalRing S]
    {κsep : Type*} [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
    [IsSepClosure (maximalIdeal S).ResidueField κsep]
    {Ssh : Type w} [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    (h : IsStrictHenselization S κsep Ssh) :
    Module.Flat S Ssh :=
  have : Module.Flat S (ULift.{u} Ssh) :=
    CommAlgCat.flat_of_ind_etale h.isFilteredColimitEtale
  Module.Flat.of_linearEquiv (ULift.algEquiv : ULift.{u} Ssh ≃ₐ[S] Ssh).symm.toLinearEquiv

end Stacks.StrictHenselization

end
