module

public import StacksFrontier.RingTheory.Flat.CompleteDevissageChain

/-!
# Assembling a complete dévissage at a prime one stage at a time

A complete dévissage of `N/S/R` *at* a prime `q` of `S` (Stacks 05HZ) is recorded by
`Module.NonemptyCompleteDevissageAt` as a complete dévissage over `q.under R` together with a
compatible system of primes of its stage algebras. The construction that produces one is
recursive, exactly as in the unpointed case: a scheme-theoretic complete dévissage at a point is
a pointed head stage followed by a complete dévissage of the cokernel at the head stage's
distinguished point, and translating it into algebra needs the ability to put one pointed stage
in front of a pointed dévissage of that cokernel.

The obstacle is that the base prime of `Module.NonemptyCompleteDevissageAt R S N q` is not a
parameter: it is `q.under R`, computed from `q`. A recursion through it would therefore change
base prime at every step — the tail of a chain is a dévissage of the cokernel at a prime `q₁` of
the *next* algebra, whose base prime `q₁.under R` is only propositionally equal to `q.under R` —
and every stage would have to be transported along that equality.

This file removes the transport by splitting the two roles of the base prime.
`Module.PointedCompleteDevissage R S N r q` is a complete dévissage over a prime `r` of `R` given
*independently* of `q`, together with the pointed datum of each of its stages and the two
compatibility conditions on the chosen primes. The base prime `r` is then fixed along the whole
recursion, and `Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt` identifies it with
`q.under R` once, at the end.

## Main definitions

* `Module.PointedCompleteDevissage R S N r q` is a complete dévissage of `N/S/R` over the prime
  `r` of `R` whose stages carry pointed data compatible with the prime `q` of `S`.
* `Module.PointedCompleteDevissage.ofStage` is the pointed dévissage consisting of a single
  pointed stage whose map is surjective, and `Module.PointedCompleteDevissage.cons` prepends a
  pointed stage to a pointed dévissage of a module identified with the cokernel of that stage.

## Main results

* `Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt`: **a pointed complete dévissage
  over `r` whose base prime is the contraction of `q` is a nonempty complete dévissage at `q`.**

## Implementation notes

The structure carries the family of pointed data as a function on the stages of the underlying
dévissage, so that `Module.PointedCompleteDevissage.cons` can prepend to it with
`Module.DevissageStageData.consPointed`, i.e. by prepending to a single family of stages.
That is the same discipline as in `Module.CompleteDevissage.consStageData`, and for the same
reason: a field-by-field `Fin.cons` makes the unifier reduce `Fin.cons` against a different large
dependent motive for every field, while prepending to one family of stages keeps the motive
constant. The index arithmetic that relates the two indexings holds definitionally, so the two
compatibility conditions of a prepended dévissage are literally `Fin.cons` of the head link and
the tail's own conditions.

The tail of `Module.PointedCompleteDevissage.cons` is a pointed dévissage at the *lower* prime of
the head stage, over the same `r`. The head link of `Module.NonemptyCompleteDevissageAt`, that
the tail's first upper prime contracts to the head's lower prime, is therefore the tail's own
`initial_under` and needs no separate hypothesis.

`Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt` substitutes the equation
`q.under R = r` rather than transporting along it. The `Ideal.IsPrime` arguments of
`Module.CompleteDevissage` and of `Module.NonemptyCompleteDevissageAt` are `Prop`-valued, so the
proof of primality carried by `r` and the one instance synthesis finds for `q.under R` give the
same type and nothing more is needed.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
-/

@[expose] public noncomputable section

universe u v w

namespace Module

/-- A complete dévissage of `N/S/R` over a prime `r` of `R` whose stages carry the pointed data
of Stacks 05HZ, compatible with a prime `q` of `S`.

Unlike `Module.NonemptyCompleteDevissageAt`, whose base prime is forced to be `q.under R`, this
records the base prime `r` as an independent parameter. That is what lets a stage be prepended to
a pointed dévissage of its cokernel without transporting the stages along the equality of base
primes; see `Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt`. -/
public structure PointedCompleteDevissage (R : Type u) (S : Type v) (N : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] where
  /-- The underlying complete dévissage over `r`. -/
  toCompleteDevissage : CompleteDevissage R S N r
  /-- The pointed datum of each stage. -/
  pointed : ∀ i, (toCompleteDevissage.stages i).Pointed
  /-- The prime `q` is the contraction of the first upper prime. -/
  initial_under : (pointed 0).upperPrime.comap toCompleteDevissage.toA₀.toRingHom = q
  /-- Consecutive stages carry compatible primes. -/
  transition_under : ∀ i : Fin toCompleteDevissage.stepCount,
    (pointed i.succ).upperPrime.comap (toCompleteDevissage.toRight i).toRingHom =
      (pointed i.castSucc).lowerPrime

namespace PointedCompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime] {q : Ideal S} [q.IsPrime]

/-- A single pointed stage whose map is surjective, together with a presentation of the algebra
being dévissed, an identification of the module being dévissed and the contraction of the stage's
upper prime to `q`, is a pointed complete dévissage. This is the base case of the recursion,
matching `AlgebraicGeometry.PointedDevissageChain.last`. -/
public def ofStage (st : DevissageStageData.{u, w} R r) (P : st.Pointed) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha)
    (hinit : P.upperPrime.comap toA.toRingHom = q) :
    PointedCompleteDevissage R S N r q where
  toCompleteDevissage := CompleteDevissage.ofStage st toA hsurj hfp equiv hfinal
  pointed := fun _ => P
  initial_under := hinit
  transition_under := fun i => i.elim0

/-- Prepending a pointed stage to a pointed complete dévissage of its cokernel, taken at the
stage's lower prime, gives a pointed complete dévissage. This is the recursive step, matching
`AlgebraicGeometry.PointedDevissageChain.more`.

The tail dévisses an arbitrary module `N'` identified with the cokernel of the stage by `e`, as in
`Module.CompleteDevissage.consStageData`. Because the tail is taken *at the stage's lower
prime*, its own `initial_under` is the compatibility of the first two stages and no further
hypothesis is needed. -/
public def cons (st : DevissageStageData.{u, w} R r) (P : st.Pointed) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N')
    (E : letI := P.lowerPrime_isPrime
      PointedCompleteDevissage R st.B N' r P.lowerPrime)
    (hinit : P.upperPrime.comap toA.toRingHom = q) :
    PointedCompleteDevissage R S N r q :=
  letI := P.lowerPrime_isPrime
  { toCompleteDevissage :=
      CompleteDevissage.consStageData st toA hsurj hfp equiv e E.toCompleteDevissage
    pointed := st.consPointed E.toCompleteDevissage.stages P E.pointed
    initial_under := hinit
    transition_under := Fin.cons E.initial_under E.transition_under }

/-- **A pointed complete dévissage over `r` whose base prime is the contraction of `q` is a
nonempty complete dévissage at `q`.**

This is where the base prime recorded independently is identified with the one
`Module.NonemptyCompleteDevissageAt` computes, and it is the only point of the construction at
which that identification is used. -/
public def toNonemptyCompleteDevissageAt (hrq : q.under R = r)
    (E : PointedCompleteDevissage R S N r q) : NonemptyCompleteDevissageAt R S N q := by
  subst hrq
  exact
    { toCompleteDevissage := E.toCompleteDevissage
      lowerPrime := fun i => (E.pointed i).lowerPrime
      lowerPrime_isPrime := fun i => (E.pointed i).lowerPrime_isPrime
      lowerPrime_liesOver := fun i => (E.pointed i).lowerPrime_liesOver
      residueField_purelyTranscendental := fun i =>
        (E.pointed i).residueField_purelyTranscendental
      upperPrime := fun i => (E.pointed i).upperPrime
      upperPrime_isPrime := fun i => (E.pointed i).upperPrime_isPrime
      upperPrime_under := fun i => (E.pointed i).upperPrime_under
      upperPrime_unique := fun i => (E.pointed i).upperPrime_unique
      initial_under := E.initial_under
      transition_under := E.transition_under
      lowerPrime_mem_fiberSupport := fun i => (E.pointed i).lowerPrime_mem_fiberSupport
      relativeDimension_eq_support := fun i => (E.pointed i).relativeDimension_eq_support }

end PointedCompleteDevissage

end Module

end
