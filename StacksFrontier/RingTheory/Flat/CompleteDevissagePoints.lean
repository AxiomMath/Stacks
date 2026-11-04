module

public import StacksFrontier.RingTheory.Flat.CompleteDevissage

/-!
# The primes of a complete dévissage at a point

A complete dévissage of `N/S/R` at a prime `q` of `S` (Stacks Tag 05HZ) records, besides the
stage data, a prime `pᵢ` of every lower algebra `Bᵢ` and the unique prime `Pᵢ` of `Aᵢ` above it,
compatible with the initial and transition maps. This file isolates exactly that part of the
data: it is what the proof of Stacks Tag 05PG uses of a dévissage at a point, and unlike the
pure transcendence, support and dimension conditions of Stacks Tag 05HZ it survives a
localization of the base without further work.

## Main definitions

* `Module.CompleteDevissage.Points D q`: primes of the stages of `D` over the base prime,
  compatible with `q`.
* `Module.NonemptyCompleteDevissageAt.points`: the primes a dévissage at `q` records.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

universe u v w

namespace Module

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

/-- Primes of the stages of a complete dévissage `D` over `r`, compatible with a prime `q` of
`S`: a prime `p i` of every lower algebra lying over `r`, the unique prime `P i` of the upper
algebra above it, the contraction of `P 0` to `S` being `q` and the contraction of `P (i + 1)`
to the previous lower algebra being `p i`. -/
structure Points (D : CompleteDevissage R S N r) (q : Ideal S) where
  /-- The prime of each lower algebra. -/
  p : ∀ i, Ideal (D.B i)
  /-- Each lower prime is prime. -/
  isPrime_p : ∀ i, (p i).IsPrime
  /-- Each lower prime lies over the base prime. -/
  comap_p : ∀ i, (p i).comap (algebraMap R (D.B i)) = r
  /-- The prime of each upper algebra. -/
  P : ∀ i, Ideal (D.A i)
  /-- Each upper prime is prime. -/
  isPrime_P : ∀ i, (P i).IsPrime
  /-- Each upper prime lies over the lower prime of its stage. -/
  comap_P : ∀ i, (P i).comap (D.toLeft i).toRingHom = p i
  /-- Each upper prime is the only prime above the lower prime of its stage. -/
  unique_P : ∀ i (P' : Ideal (D.A i)), P'.IsPrime →
    P'.comap (D.toLeft i).toRingHom = p i → P' = P i
  /-- The first upper prime contracts to `q`. -/
  initial : (P 0).comap D.toA₀.toRingHom = q
  /-- Each upper prime contracts to the lower prime of the previous stage. -/
  transition : ∀ j : Fin D.stepCount, (P j.succ).comap (D.toRight j).toRingHom = p j.castSucc

end CompleteDevissage

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- The primes recorded by a nonempty complete dévissage at `q`. -/
def points (E : NonemptyCompleteDevissageAt R S N q) : E.toCompleteDevissage.Points q where
  p := E.lowerPrime
  isPrime_p := E.lowerPrime_isPrime
  comap_p i := ((E.lowerPrime_liesOver i).over).symm
  P := E.upperPrime
  isPrime_P := E.upperPrime_isPrime
  comap_P := E.upperPrime_under
  unique_P := E.upperPrime_unique
  initial := E.initial_under
  transition := E.transition_under

end NonemptyCompleteDevissageAt

end Module

end
