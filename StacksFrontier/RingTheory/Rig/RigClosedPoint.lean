module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.ClosedPoint

/-!
# Rig-closed primes of an adic topological ring

A prime `q` of a topological ring `A` is *rig-closed* when it is maximal among the primes of
`A` that do not contain some ideal of definition.  For a Noetherian adic topological ring this
is the first of the equivalent conditions collected by `Rig.rigPoint_tfae`, and the remaining
ones become characterizations of rig-closedness: `q` cuts out a closed point of the complement
of the vanishing locus of every ideal of definition, the quotient `A ⧸ q` is one-dimensional
with nondiscrete induced topology, and `A ⧸ q` is a complete one-dimensional Noetherian local
domain whose maximal ideal is the radical of every extended ideal of definition.

## Main definitions

* `Rig.Ideal.IsRigClosed` — a prime is rig-closed.

## Main results

* `Rig.isRigClosed_iff_exists_isClosedPointAwayFrom` and
  `Rig.isRigClosed_iff_forall_isClosedPointAwayFrom` — the closed-point descriptions, for some
  and for every ideal of definition.
* `Rig.isRigClosed_iff_forall_isMaximalAmongPrimesAvoiding` — maximality holds for every ideal
  of definition as soon as it holds for one.
* `Rig.isRigClosed_iff_ringKrullDim_eq_one_and_not_discreteTopology` — the dimension and
  topology description of the quotient.
* `Rig.isRigClosed_iff_isRigPointLocalCondition` — the purely algebraic description of the
  quotient as a complete one-dimensional Noetherian local domain.

## References

* [Stacks Project, Tag 0GG9](https://stacks.math.columbia.edu/tag/0GG9)
-/

@[expose] public section

namespace Rig

universe u

/-- A prime `q` of a topological ring is *rig-closed* if some ideal of definition is not
contained in `q` and `q` is maximal among the primes not containing it. -/
@[stacks 0GG9]
public def Ideal.IsRigClosed {A : Type u} [CommRing A] [TopologicalSpace A]
    (q : Ideal A) : Prop :=
  ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
    Ideal.IsMaximalAmongPrimesAvoiding I q

section

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsNoetherianRing A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
  [T2Space A]

/-- A prime is rig-closed exactly when it cuts out a closed point of the complement of the
vanishing locus of some ideal of definition. -/
public theorem isRigClosed_iff_exists_isClosedPointAwayFrom
    (hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsRigClosed q ↔
      ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
        Ideal.IsClosedPointAwayFrom I q :=
  (rigPoint_tfae hadic q).out 1 2

/-- A prime is rig-closed exactly when it is maximal among the primes avoiding every ideal of
definition. -/
public theorem isRigClosed_iff_forall_isMaximalAmongPrimesAvoiding
    (hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsRigClosed q ↔
      ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
        Ideal.IsMaximalAmongPrimesAvoiding I q :=
  (rigPoint_tfae hadic q).out 1 3

/-- A prime is rig-closed exactly when it cuts out a closed point of the complement of the
vanishing locus of every ideal of definition. -/
public theorem isRigClosed_iff_forall_isClosedPointAwayFrom
    (hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsRigClosed q ↔
      ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
        Ideal.IsClosedPointAwayFrom I q :=
  (rigPoint_tfae hadic q).out 1 4

/-- A prime is rig-closed exactly when the quotient is one-dimensional and carries a
nondiscrete induced topology. -/
public theorem isRigClosed_iff_ringKrullDim_eq_one_and_not_discreteTopology
    (hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsRigClosed q ↔ ringKrullDim (A ⧸ q) = 1 ∧ ¬ DiscreteTopology (A ⧸ q) :=
  (rigPoint_tfae hadic q).out 1 7

/-- A prime is rig-closed exactly when the quotient is a complete one-dimensional Noetherian
local domain whose maximal ideal is the radical of every extended ideal of definition. -/
public theorem isRigClosed_iff_isRigPointLocalCondition
    (hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsRigClosed q ↔ Ideal.IsRigPointLocalCondition q :=
  (rigPoint_tfae hadic q).out 1 8

end

end Rig

end
