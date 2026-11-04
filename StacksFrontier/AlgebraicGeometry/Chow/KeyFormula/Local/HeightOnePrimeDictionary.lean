module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# Height-one primes of a local ring and the codimension-one points above it

Let `X` be a scheme, let `x` be a point of it and let `A = 𝒪_{X, x}`. The canonical morphism
`AlgebraicGeometry.Scheme.fromSpecStalk` has as its range the set of points of `X` that
specialize to `x` (`AlgebraicGeometry.Scheme.range_fromSpecStalk`, Stacks 01J7), it is a
topological embedding, and under the identification it gives, the height of a prime of `A` is the
coheight of the point of `X` it cuts out (Stacks 02IZ read at a prime rather than at the maximal
ideal). This file reads off the dictionary the key formula Stacks 0AYC needs at a codimension-two
point `x`: the height-one primes of `A` -- the index set of the local reciprocity law
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero` -- are exactly the codimension-one
points of `X` specializing to `x`, that is, the prime divisors of `X` through `x`.

The index set here is `Stacks.Chow.HeightOnePrime A`, the one the tame symbol sums of Stacks 0EAX
are indexed by. No hypothesis on `x` is needed for any statement below: the coheight of the point
cut out by a prime is the height of that prime whatever the dimension of `A`, and the case
`Order.coheight x = 2` is only the case in which the key formula has content.

## Main definitions

* `Stacks.Chow.pointOfHeightOnePrime` — the point of `X` cut out by a height-one prime of
  `𝒪_{X, x}`, namely its image under `Spec 𝒪_{X, x} ⟶ X`.
* `Stacks.Chow.heightOnePrimeEquivCoheightOneGenerization` — **the dictionary**: the height-one
  primes of `𝒪_{X, x}` are in bijection with the coheight-one points of `X` specializing to `x`.

## Main results

* `Stacks.Chow.pointOfHeightOnePrime_specializes` — the point cut out by a height-one prime
  specializes to `x`.
* `Stacks.Chow.coheight_pointOfHeightOnePrime` — it has coheight one, so it is the generic point
  of a prime divisor of `X`.
* `Stacks.Chow.pointOfHeightOnePrime_injective` — distinct height-one primes cut out distinct
  points.
* `Stacks.Chow.exists_pointOfHeightOnePrime_eq` — every coheight-one point specializing to `x` is
  cut out by a height-one prime.

## References

* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The point of `X` cut out by a height-one prime `𝔮` of `A = 𝒪_{X, x}`: the image of `𝔮` under
the canonical morphism `Spec A ⟶ X`. -/
def pointOfHeightOnePrime {x : X} (p : HeightOnePrime (X.presheaf.stalk x)) : X :=
  (X.fromSpecStalk x).base p.1

/-- The point cut out by a height-one prime of `𝒪_{X, x}` specializes to `x`, the range of
`Spec 𝒪_{X, x} ⟶ X` being the set of generizations of `x`. -/
theorem pointOfHeightOnePrime_specializes {x : X} (p : HeightOnePrime (X.presheaf.stalk x)) :
    pointOfHeightOnePrime p ⤳ x :=
  specializes_fromSpecStalk x p.1

/-- **The point cut out by a height-one prime of `𝒪_{X, x}` has codimension one.** Its coheight
is the height of the prime, by Stacks 02IZ read at that prime. -/
theorem coheight_pointOfHeightOnePrime {x : X} (p : HeightOnePrime (X.presheaf.stalk x)) :
    coheight (pointOfHeightOnePrime p) = 1 :=
  (coheight_fromSpecStalk_eq_height x p.1).trans p.2

/-- Distinct height-one primes of `𝒪_{X, x}` cut out distinct points of `X`, because
`Spec 𝒪_{X, x} ⟶ X` is a topological embedding. -/
theorem pointOfHeightOnePrime_injective {x : X} :
    Function.Injective (pointOfHeightOnePrime (X := X) (x := x)) := fun _ _ h =>
  Subtype.ext ((X.fromSpecStalk x).isEmbedding.injective h)

/-- **Every codimension-one point specializing to `x` comes from a height-one prime of
`𝒪_{X, x}`.** It comes from a prime because it specializes to `x`, and that prime has height one
because the height is the coheight of the point. -/
theorem exists_pointOfHeightOnePrime_eq {x z : X} (hzx : z ⤳ x) (hz : coheight z = 1) :
    ∃ p : HeightOnePrime (X.presheaf.stalk x), pointOfHeightOnePrime p = z := by
  obtain ⟨p, rfl⟩ := exists_fromSpecStalk_eq hzx
  exact ⟨⟨p, (coheight_fromSpecStalk_eq_height x p).symm.trans hz⟩, rfl⟩

/-- **The dictionary between height-one primes and codimension-one points.** For a point `x` of a
scheme `X`, the height-one primes of `A = 𝒪_{X, x}` correspond bijectively to the points of `X`
of coheight one that specialize to `x`, a prime `𝔮` going to the point it cuts out under
`Spec A ⟶ X`.

At a codimension-two point `x` of an integral, locally Noetherian scheme this is the index
correspondence the key formula Stacks 0AYC uses to read the local reciprocity law of Stacks 0EAX,
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero`, as a sum over the prime divisors
through `x`. -/
def heightOnePrimeEquivCoheightOneGenerization (x : X) :
    HeightOnePrime (X.presheaf.stalk x) ≃ {z : X // z ⤳ x ∧ coheight z = 1} :=
  Equiv.ofBijective
    (fun p => ⟨pointOfHeightOnePrime p, pointOfHeightOnePrime_specializes p,
      coheight_pointOfHeightOnePrime p⟩)
    ⟨fun _ _ h => pointOfHeightOnePrime_injective (congrArg Subtype.val h :),
      fun z => (exists_pointOfHeightOnePrime_eq z.2.1 z.2.2).imp fun _ hp => Subtype.ext hp⟩

/-- The point of `X` attached to a height-one prime `p` of `𝒪_{X, x}` by
`heightOnePrimeEquivCoheightOneGenerization` is `pointOfHeightOnePrime p`. -/
@[simp] theorem heightOnePrimeEquivCoheightOneGenerization_apply (x : X)
    (p : HeightOnePrime (X.presheaf.stalk x)) :
    (heightOnePrimeEquivCoheightOneGenerization x p : X) = pointOfHeightOnePrime p := rfl

end Stacks.Chow

end
