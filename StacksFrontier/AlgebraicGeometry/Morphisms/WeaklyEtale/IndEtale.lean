module

public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksCore.Tactic.StacksAttribute

/-!
# Ind-étale ring maps are weakly étale

An algebra which is a filtered colimit of étale algebras is weakly étale.

## Main results

* `Algebra.weaklyEtale_of_ind_etale`: an ind-étale algebra is weakly étale.

## Implementation notes

Ind-étaleness is expressed by `StacksDraft.IndEtale`, which represents a filtered colimit of
étale algebras even when the base and target rings lie in different universes. The conclusion
uses Mathlib's class `Algebra.WeaklyEtale`.

## References

* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
-/

@[expose] public section

universe u v

namespace Algebra

/-- The universe-monomorphic form of `Algebra.weaklyEtale_of_ind_etale`: it is obtained by
transporting the two rings into a common universe along the canonical `ULift` equivalences. -/
private theorem weaklyEtale_of_indEtale {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (h : StacksDraft.IndEtale A B) : Algebra.WeaklyEtale A B := by
  let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A (ULift.{u} B)
  obtain ⟨J, _, _, pres, hp⟩ := StacksDraft.indEtale_iff.mp
    (StacksDraft.indEtale_of_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm
      (fun _ => rfl) h)
  exact Algebra.WeaklyEtale.ulift_iff.mp
    ((weaklyEtale_of_isLocalization_etale_filteredColimit.{max u v, max u v, max u v}
      (ULift.{v} A)).2.2 J pres.diag pres.cocone pres.isColimit
      (fun j => by let : Algebra.Etale (ULift.{v} A) (pres.diag.obj j) := hp j
                   infer_instance))

/-- **Stacks Project, Tag 097N.** A filtered colimit of étale algebras is weakly étale. -/
@[stacks 097N]
theorem weaklyEtale_of_ind_etale {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (h : StacksDraft.IndEtale A B) :
    Algebra.WeaklyEtale A B := weaklyEtale_of_indEtale h

end Algebra
