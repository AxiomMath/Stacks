module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder
public import StacksFrontier.RingTheory.Kaehler.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The divisor of zeros and poles of a rational differential

Let `X` be an integral locally Noetherian scheme with function field `R(X)`, let `K` be a ring
identified with `R(X)`, and let `ω ∈ Ω[K⁄k]` be a differential of `K` over a base ring `k`. The
**divisor of zeros and poles of `ω`** is the Weil divisor whose coefficient at a prime divisor
`Z` is computed as follows: pick a rational function `t` of order one at `Z`, write `ω = g · dt`,
and take the order of vanishing of `g` at `Z`. On a nonsingular curve over a field this is the
canonical divisor `K_C` of the final-exam situation Stacks 09U0.

The coefficient is read off a sheaf of differentials only through the data recorded in
`Stacks.Divisors.IsDivisorOfRationalDifferential`, so that predicate mentions no sheaf at all:
it is a condition relating a Weil divisor on `X`, the identification of `K` with `R(X)`, and the
orders of vanishing of rational functions. The existence of a divisor satisfying it is supplied
by the meromorphic-section order of `Stacks.Divisors.weilDivisorOfMeromorphicSection`, applied
to the image of `ω` in the generic stalk of an invertible module `L` that realizes the rational
differentials — for the canonical divisor, `L = Ω_{X⁄k}`. The two facts that realization has to
satisfy are exactly the hypotheses of
`Stacks.Divisors.isDivisorOfRationalDifferential_weilDivisorOfMeromorphicSection`: the
realization is semilinear over the identification, and `dt` is realized by a basis of the stalk
of `L` at `Z` whenever `t` has order one at `Z`.

## Main definitions

* `Stacks.Divisors.IsDivisorOfRationalDifferential`: a Weil divisor is the divisor of zeros and
  poles of a rational differential.

## Main results

* `Stacks.Divisors.isDivisorOfRationalDifferential_weilDivisorOfMeromorphicSection`: the Weil
  divisor of the meromorphic section realizing `ω` is the divisor of zeros and poles of `ω`.
* `Stacks.Divisors.exists_isDivisorOfRationalDifferential`: consequently a rational differential
  realized by an invertible module has a divisor of zeros and poles.

## Implementation notes

The condition is stated for *every* pair `(t, g)` with `t` of order one at `Z` and `ω = g · dt`,
which simultaneously says that the coefficient is what the source says it is and that it does
not depend on the choice; nothing asserts that such a pair exists, so the predicate is a
condition on the divisor rather than a construction of it. It is exactly the shape in which
`Stacks.Chow.principalDivisor` (Stacks 0BE3) describes the principal divisor of a rational
function, and the order of vanishing used is the same `AlgebraicGeometry.Scheme.ord`, so
canonical and principal divisors are measured by one valuation.

Invertibility of the realizing module enters only through `Stacks.Divisors.IsTrivializedNear`,
carried as an explicit hypothesis as everywhere else in this tree.

## References

* [Stacks Project, Tag 09U0](https://stacks.math.columbia.edu/tag/09U0)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.Divisors

variable {k : Type v} [CommRing k] {K : Type u} [CommRing K] [Algebra k K]

/-- **Stacks 09U0.** A Weil divisor `D` on `X` is the **divisor of zeros and poles** of the
rational differential `ω ∈ Ω[K⁄k]`, read through an identification `e` of `K` with the function
field of `X`, when its coefficient at every prime divisor `Z` is the order of vanishing at `Z`
of every `g` for which `ω = g · dt` with `t` of order one at `Z`.

On a nonsingular projective curve over a field, taking `ω` to be the distinguished differential
of an irreducible plane curve makes this the canonical divisor `K_C`. -/
@[stacks 09U0 "the divisor of zeros and poles of ω"]
def IsDivisorOfRationalDifferential (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (e : K ≃+* X.functionField) (ω : Ω[K⁄k]) (D : WeilDivisor X) : Prop :=
  ∀ (Z : PrimeDivisor X) (t g : K), X.ord (e t) Z.genericPoint = 1 →
    ω = g • KaehlerDifferential.D k K t → D.val Z = X.ord (e g) Z.genericPoint

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules}

/-- **Stacks 09U0.** The divisor of zeros and poles of a rational differential exists as soon as
the differential is realized in an invertible module.

Let `L` be a module on `X` that is trivialized near every point, and let `E` realize the
rational differentials of `K` over `k` inside the generic stalk of `L`, semilinearly over the
identification `e` of `K` with `R(X)`. If `dt` is realized by a basis of the stalk of `L` at the
generic point of `Z` whenever `t` has order one at `Z` — which is the local structure of the
sheaf of differentials on a nonsingular curve — then the Weil divisor of `E ω`, regarded as a
meromorphic section of `L`, is the divisor of zeros and poles of `ω`. -/
@[stacks 09U0 "the divisor of zeros and poles of ω"]
theorem isDivisorOfRationalDifferential_weilDivisorOfMeromorphicSection
    (hL : ∀ x : X, IsTrivializedNear L x) (e : K ≃+* X.functionField)
    (E : Ω[K⁄k] →+ L.presheaf.stalk (genericPoint X))
    (hE : ∀ (g : K) (ν : Ω[K⁄k]), E (g • ν) = e g • E ν) (ω : Ω[K⁄k])
    (hbasis : ∀ (Z : PrimeDivisor X) (t : K), X.ord (e t) Z.genericPoint = 1 →
      ∃ m : L.presheaf.stalk Z.genericPoint, IsStalkBasis L Z.genericPoint m ∧
        toGenericStalk L Z.genericPoint m = E (KaehlerDifferential.D k K t)) :
    IsDivisorOfRationalDifferential X e ω (weilDivisorOfMeromorphicSection hL (E ω)) := by
  intro Z t g ht hωg
  obtain ⟨m, hm, hmt⟩ := hbasis Z t ht
  rw [weilDivisorOfMeromorphicSection_apply]
  exact orderOfVanishing_eq (hL _) ⟨m, hm, by rw [hmt, ← hE, hωg]⟩

/-- **Stacks 09U0.** A rational differential realized in a module trivialized near every point,
whose exact differentials at uniformizers are bases of the stalks, has a divisor of zeros and
poles. -/
@[stacks 09U0 "the divisor of zeros and poles of ω"]
theorem exists_isDivisorOfRationalDifferential
    (hL : ∀ x : X, IsTrivializedNear L x) (e : K ≃+* X.functionField)
    (E : Ω[K⁄k] →+ L.presheaf.stalk (genericPoint X))
    (hE : ∀ (g : K) (ν : Ω[K⁄k]), E (g • ν) = e g • E ν) (ω : Ω[K⁄k])
    (hbasis : ∀ (Z : PrimeDivisor X) (t : K), X.ord (e t) Z.genericPoint = 1 →
      ∃ m : L.presheaf.stalk Z.genericPoint, IsStalkBasis L Z.genericPoint m ∧
        toGenericStalk L Z.genericPoint m = E (KaehlerDifferential.D k K t)) :
    ∃ D : WeilDivisor X, IsDivisorOfRationalDifferential X e ω D :=
  ⟨_, isDivisorOfRationalDifferential_weilDivisorOfMeromorphicSection hL e E hE ω hbasis⟩

end Stacks.Divisors

end
