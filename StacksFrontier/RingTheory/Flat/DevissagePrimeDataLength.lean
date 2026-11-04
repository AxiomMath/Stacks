module

public import StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk05I7
public import StacksFrontier.RingTheory.Flat.DevissageLength

/-!
# The recursion of Stacks 05I1 carrying the stage primes

`StacksFrontier.RingTheory.Flat.DevissageLength` supplies the two halves of the recursion by which
Stacks 05I1 builds a complete dévissage: a stage whose map is surjective already is a complete
dévissage of length one (`Module.DevissageStage.toCompleteDevissage`), and a stage together with a
complete dévissage of the cokernel of its map is a complete dévissage with one more stage
(`Module.CompleteDevissage.cons`).

Neither half carries the *stage primes*. Those are `Module.CompleteDevissage.PrimeData`, the nine
conditions on a compatible system of primes which
`Module.CompleteDevissage.finitePresentation_of_flat` — the conclusion of Stacks 05I4 — consumes,
and which is what the obligation
`Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage` asks for. This file supplies the prime
data for both halves, so that the recursion can be run at the level of a dévissage *with* its
prime data rather than of a bare dévissage:

* `Module.CompleteDevissage.PrimeData.ofStage` is the base case: the prime data of the length-one
  dévissage of a stage whose map is surjective;
* `Module.CompleteDevissage.PrimeData.cons` is the inductive step: the prime data of
  `Module.CompleteDevissage.cons` from a prime of the lower algebra of the stage, the unique prime
  of its upper algebra above that one, and prime data for the dévissage of the cokernel **over
  that same prime of the lower algebra**.

The two existence statements
`Module.DevissageStage.exists_primeData_of_surjective_alpha` and
`Module.DevissageStage.exists_primeData_of_exists_primeData_cokernel` package them in the shape
`∃ D, Nonempty (D.PrimeData q)` in which
`Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage` states its dévissage clause.

## Main definitions

* `Module.CompleteDevissage.PrimeData.ofStage`
* `Module.CompleteDevissage.PrimeData.cons`

## Main results

* `Module.DevissageStage.exists_primeData_of_surjective_alpha`
* `Module.DevissageStage.exists_primeData_of_exists_primeData_cokernel`

## Implementation notes

`Module.CompleteDevissage.PrimeData.cons` takes no data beyond the stage primes of the one stage
being prepended and the prime data of the shorter dévissage, exactly as
`Module.CompleteDevissage.cons` takes no data beyond the stage and the shorter dévissage. The
reason is the same: the condition that the new first transition `B₀ → A₁` carries the second upper
prime to the first lower prime is literally `Module.CompleteDevissage.PrimeData.initial_under` of
the shorter dévissage, because the transition map of `Module.CompleteDevissage.cons` at index zero
is the initial map of the shorter dévissage and the first lower prime is the prime over which the
shorter dévissage's prime data is taken. So the prime of `B₀` at which the recursion continues is
forced to be the first lower prime, and it appears in the statements below as `q₀`.

Every field is `Module.CompleteDevissage.finCases` of the corresponding datum of the stage and of
the shorter dévissage, and each reduces definitionally, for the reasons recorded in
`StacksFrontier.RingTheory.Flat.DevissageLength`: the case split reduces by `Nat` iota, and
`Fin.succ_castSucc` holds by `rfl`, which is what makes the transition condition at a successor
index be the transition condition of the shorter dévissage without a transport.

No `@[stacks]` attribute is placed here. Stacks 05I1 asserts the *existence* of an elementary
étale localization together with a complete dévissage of the localized module; what is proved here
is the step of its recursion which assembles the dévissage once the stages are given, which is not
by itself any numbered statement of the source.

## References

* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
-/

@[expose] public section

universe u v w

namespace Module.CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- **The stage primes of the length-one dévissage of a stage whose map is surjective.**

This is the base case of the recursion of Stacks 05I1 at the level of a dévissage together with
its prime data: the single stage carries the prime `q₀` of its lower algebra, contracting to the
prime `r` of the base, and the unique prime `p₀` of its upper algebra above `q₀`, contracting to
the given prime `q` of `S`. There are no transitions to check. -/
def PrimeData.ofStage (E : DevissageStage R S N r) (hsurj : Function.Surjective E.alpha)
    {q : Ideal S} (q₀ : Ideal E.B) (hq₀prime : q₀.IsPrime)
    (hq₀under : q₀.comap (algebraMap R E.B) = r) (p₀ : Ideal E.A) (hp₀prime : p₀.IsPrime)
    (hp₀under : p₀.comap E.toLeft.toRingHom = q₀)
    (hp₀unique : ∀ t : Ideal E.A, t.IsPrime → t.comap E.toLeft.toRingHom = q₀ → t = p₀)
    (hp₀init : p₀.comap E.toA₀.toRingHom = q) :
    (E.toCompleteDevissage hsurj).PrimeData q where
  lowerPrime _ := q₀
  lowerPrime_isPrime _ := hq₀prime
  lowerPrime_under _ := hq₀under
  upperPrime _ := p₀
  upperPrime_isPrime _ := hp₀prime
  upperPrime_under _ := hp₀under
  upperPrime_unique _ := hp₀unique
  initial_under := hp₀init
  transition_under i := Fin.elim0 i

/-- **Prepending the stage primes of one stage to the prime data of a dévissage of its cokernel.**

This is the inductive step of the recursion of Stacks 05I1 at the level of a dévissage together
with its prime data. The prepended stage carries a prime `q₀` of its lower algebra over `r` and
the unique prime `p₀` of its upper algebra above `q₀`, contracting to `q`; the dévissage of the
cokernel carries prime data over that same `q₀`, and that is exactly what the new first transition
condition needs. -/
def PrimeData.cons (E : DevissageStage R S N r)
    (D : CompleteDevissage R E.B (E.M ⧸ LinearMap.range E.alpha) r) {q : Ideal S}
    {q₀ : Ideal E.B} (hq₀prime : q₀.IsPrime) (hq₀under : q₀.comap (algebraMap R E.B) = r)
    (p₀ : Ideal E.A) (hp₀prime : p₀.IsPrime) (hp₀under : p₀.comap E.toLeft.toRingHom = q₀)
    (hp₀unique : ∀ t : Ideal E.A, t.IsPrime → t.comap E.toLeft.toRingHom = q₀ → t = p₀)
    (hp₀init : p₀.comap E.toA₀.toRingHom = q) (pd : D.PrimeData q₀) :
    (CompleteDevissage.cons E D).PrimeData q where
  lowerPrime := finCases q₀ pd.lowerPrime
  lowerPrime_isPrime := finCases hq₀prime pd.lowerPrime_isPrime
  lowerPrime_under := finCases hq₀under pd.lowerPrime_under
  upperPrime := finCases p₀ pd.upperPrime
  upperPrime_isPrime := finCases hp₀prime pd.upperPrime_isPrime
  upperPrime_under := finCases hp₀under pd.upperPrime_under
  upperPrime_unique := finCases hp₀unique pd.upperPrime_unique
  initial_under := hp₀init
  transition_under := finCases pd.initial_under pd.transition_under

end Module.CompleteDevissage

namespace Module.DevissageStage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- **The base case of the recursion of Stacks 05I1, with prime data.**

A stage whose map is surjective and which carries a prime of its lower algebra over `r` together
with the unique prime of its upper algebra above it contracting to `q` gives a complete dévissage
of `N/S/R` over `r` with prime data over `q` — the shape in which
`Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage` states its dévissage clause. -/
theorem exists_primeData_of_surjective_alpha (E : DevissageStage R S N r)
    (hsurj : Function.Surjective E.alpha) {q : Ideal S} (q₀ : Ideal E.B) (hq₀prime : q₀.IsPrime)
    (hq₀under : q₀.comap (algebraMap R E.B) = r) (p₀ : Ideal E.A) (hp₀prime : p₀.IsPrime)
    (hp₀under : p₀.comap E.toLeft.toRingHom = q₀)
    (hp₀unique : ∀ t : Ideal E.A, t.IsPrime → t.comap E.toLeft.toRingHom = q₀ → t = p₀)
    (hp₀init : p₀.comap E.toA₀.toRingHom = q) :
    ∃ D : CompleteDevissage R S N r, Nonempty (D.PrimeData q) :=
  ⟨E.toCompleteDevissage hsurj, ⟨CompleteDevissage.PrimeData.ofStage E hsurj q₀ hq₀prime hq₀under
    p₀ hp₀prime hp₀under hp₀unique hp₀init⟩⟩

/-- **The inductive step of the recursion of Stacks 05I1, with prime data.**

If the cokernel of the map of a stage carries a complete dévissage over the lower algebra of that
stage with prime data over the stage's lower prime `q₀`, then `N/S/R` carries a complete dévissage
over `r` with prime data over `q`. -/
theorem exists_primeData_of_exists_primeData_cokernel (E : DevissageStage R S N r)
    {q : Ideal S} {q₀ : Ideal E.B} (hq₀prime : q₀.IsPrime)
    (hq₀under : q₀.comap (algebraMap R E.B) = r) (p₀ : Ideal E.A) (hp₀prime : p₀.IsPrime)
    (hp₀under : p₀.comap E.toLeft.toRingHom = q₀)
    (hp₀unique : ∀ t : Ideal E.A, t.IsPrime → t.comap E.toLeft.toRingHom = q₀ → t = p₀)
    (hp₀init : p₀.comap E.toA₀.toRingHom = q)
    (h : ∃ D : CompleteDevissage R E.B (E.M ⧸ LinearMap.range E.alpha) r,
      Nonempty (D.PrimeData q₀)) :
    ∃ D : CompleteDevissage R S N r, Nonempty (D.PrimeData q) := by
  obtain ⟨D, ⟨pd⟩⟩ := h
  exact ⟨CompleteDevissage.cons E D, ⟨CompleteDevissage.PrimeData.cons E D hq₀prime hq₀under p₀
    hp₀prime hp₀under hp₀unique hp₀init pd⟩⟩

end Module.DevissageStage

end
