module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity under universe lifting

`ULift.{v} R` is the copy of a semiring `R : Type u` in `Type (max u v)`, and
`ULift.ringEquiv : ULift.{v} R ≃+* R` is the ring isomorphism between them. Being Noetherian
depends only on the lattice of ideals, which a ring isomorphism preserves, so the lift of a
Noetherian semiring is Noetherian.

This is recorded as an instance rather than a transport lemma because it is needed at
*statement* elaboration time: a result whose base ring is a fixed ring such as `ℤ` is pinned to
that ring's universe, and the way to state it in an arbitrary universe is to take the base to be
`ULift ℤ`, whose Noetherianity any such statement already presupposes.

## Main results

* `ULift.isNoetherianRing`: the lift of a Noetherian semiring to a larger universe is Noetherian.
-/

@[expose] public section

universe u v

/-- **The lift of a Noetherian semiring to a larger universe is Noetherian.** Transport of
`IsNoetherianRing` along `ULift.ringEquiv`. -/
instance ULift.isNoetherianRing {R : Type u} [Semiring R] [IsNoetherianRing R] :
    IsNoetherianRing (ULift.{v, u} R) :=
  isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
