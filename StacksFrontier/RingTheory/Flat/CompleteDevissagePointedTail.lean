module

public import StacksFrontier.RingTheory.Flat.CompleteDevissagePointedChain
public import StacksFrontier.RingTheory.Flat.DevissageLength

/-!
# Removing the first stage of a pointed complete dévissage

`Module.CompleteDevissage.tail` removes the first stage of a complete dévissage over a prime `r`
of `R`, leaving a complete dévissage of the cokernel of the first stage map over the first lower
algebra. This file does the same for a dévissage carrying the pointed data of Stacks 05HZ.

Nothing geometric happens: the stages of the tail *are* the stages of the original dévissage,
reindexed, so each one's pointed datum is already available and all three geometric conditions of
Stacks 05HZ — the purely transcendental residue extension, membership of the chosen prime in the
fibre support, and the equality of the relative dimension with the local dimension of that
support — are carried over unchanged. What has to be said is which prime the shortened dévissage
is pointed at: the tail begins at the map `B₀ → A₁`, so its distinguished prime of the base
algebra is the lower prime of the stage that was removed, and the head link of the tail is the
first transition condition of the original.

`Module.PointedCompleteDevissage.tail` is therefore the inverse of
`Module.PointedCompleteDevissage.cons`, as `Module.CompleteDevissage.tail` is the inverse of
`Module.CompleteDevissage.consStageData`.

## Main results

* `Module.CompleteDevissage.stages_tail`: the stages of a truncated dévissage are the later
  stages of the original.
* `Module.PointedCompleteDevissage.tail`: **what is left of a pointed complete dévissage after
  its first stage is removed**, a pointed complete dévissage at the lower prime of the stage that
  was removed.

## Implementation notes

The stage of `Module.CompleteDevissage.tail` at index `i` is the stage of the original at
`(Fin.cast h i).succ`, and `Module.CompleteDevissage.stages_tail` records that this holds
definitionally: every field of `tail` is the corresponding field of the original reindexed that
way, and `Module.CompleteDevissage.stages` is a projection of those fields. The two compatibility
conditions of the result are then literally transition conditions of the original, the index
arithmetic `(Fin.cast h i.succ).castSucc = (Fin.cast h i.castSucc).succ` holding definitionally
as well.

The result is stated over the algebra `(D.stages 0).B` and the module `(D.stages 0).coker` of the
first *stage*, rather than over `D.head.B` and `D.head.M ⧸ range D.head.alpha` in which
`Module.CompleteDevissage.tail` is stated. The two agree definitionally, and the dévissage
produced by `Module.CompleteDevissage.tail` is accepted for the underlying-dévissage field with
no transport. The reason to prefer the stage spelling is that the prime the result is pointed at
is `(E.pointed 0).lowerPrime`, whose type is `Ideal (D.stages 0).B` on the nose; written over
`D.head.B` the distinguished prime would have to be unified with that type while the instance
arguments of `Module.PointedCompleteDevissage` were still pending, and instance search then fails
to see the `R`-algebra structure of the base algebra. It is also the spelling
`Module.PointedCompleteDevissage.cons` uses for its tail.

The base prime `r` is unchanged, which is what makes the construction possible at all. For
`Module.NonemptyCompleteDevissageAt` the base prime is computed from the distinguished prime of
the algebra, and removing a stage moves that prime — from `q` to the lower prime of the first
stage — so the base prime would move with it. `Module.PointedCompleteDevissage` carries the base
prime as an independent parameter, and only
`Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt` has to know that the two agree.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
-/

@[expose] public noncomputable section

universe u v w

namespace Module

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

namespace CompleteDevissage

/-- **The stages of a truncated dévissage are the later stages of the original.** Every field of
`Module.CompleteDevissage.tail` is the corresponding field of the original reindexed by
`Fin.cast`, so this holds definitionally. -/
@[simp]
public theorem stages_tail (D : CompleteDevissage R S N r) (hpos : D.stepCount ≠ 0)
    (i : Fin (D.stepCount - 1 + 1)) :
    (D.tail hpos).stages i =
      D.stages (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

end CompleteDevissage

namespace PointedCompleteDevissage

variable {q : Ideal S} [q.IsPrime]

/-- **What is left of a pointed complete dévissage after its first stage is removed**: a pointed
complete dévissage of the cokernel of the first stage map over the first lower algebra, pointed
at the lower prime of the stage that was removed, over the same base prime `r`.

The underlying dévissage is `Module.CompleteDevissage.tail`, whose stages are the later stages of
the original; the pointed datum of each is therefore the original one, and the first
compatibility condition of the result is the first transition condition of the original. This is
the inverse of `Module.PointedCompleteDevissage.cons`. -/
public def tail (E : PointedCompleteDevissage R S N r q)
    (hpos : E.toCompleteDevissage.stepCount ≠ 0) :
    letI := (E.pointed 0).lowerPrime_isPrime
    PointedCompleteDevissage R (E.toCompleteDevissage.stages 0).B
      ((E.toCompleteDevissage.stages 0).coker) r (E.pointed 0).lowerPrime :=
  letI := (E.pointed 0).lowerPrime_isPrime
  { toCompleteDevissage := E.toCompleteDevissage.tail hpos
    pointed := fun i => E.pointed (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ
    initial_under := E.transition_under (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) 0)
    transition_under := fun i =>
      E.transition_under (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i.succ) }

/-- A truncated pointed dévissage has one stage fewer. This is what makes a recursion on the
number of stages terminate. -/
public theorem stepCount_tail (E : PointedCompleteDevissage R S N r q)
    (hpos : E.toCompleteDevissage.stepCount ≠ 0) :
    letI := (E.pointed 0).lowerPrime_isPrime
    (E.tail hpos).toCompleteDevissage.stepCount = E.toCompleteDevissage.stepCount - 1 := rfl

/-- The pointed datum of a stage of a truncated pointed dévissage is the pointed datum of the
corresponding later stage of the original. -/
public theorem pointed_tail (E : PointedCompleteDevissage R S N r q)
    (hpos : E.toCompleteDevissage.stepCount ≠ 0)
    (i : Fin (E.toCompleteDevissage.stepCount - 1 + 1)) :
    letI := (E.pointed 0).lowerPrime_isPrime
    (E.tail hpos).pointed i =
      E.pointed (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

end PointedCompleteDevissage

end Module

end
