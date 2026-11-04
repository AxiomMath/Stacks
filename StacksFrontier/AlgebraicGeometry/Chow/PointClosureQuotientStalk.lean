module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# The local ring of the closure of a point is a quotient of the local ring below it

Let `X` be a scheme, let `x''` be a point of `X` and let `𝔮` be a prime of `A = 𝒪_{X, x''}`. The
canonical morphism `AlgebraicGeometry.Scheme.fromSpecStalk` attaches to `𝔮` a point
`x' = X.fromSpecStalk x'' 𝔮` of `X` which specializes to `x''`, and the reduced closed subscheme
`closure {x'}` therefore contains `x''`. This file identifies

`A ⧸ 𝔮 ≅ 𝒪_{closure {x'}, x''}`

as a ring isomorphism, and reads the order of vanishing of Stacks 02MD across it.

Both halves of the identification are already in the development and nothing new is needed of
either: the ideal sheaf of the reduced closed subscheme spanned by `x'` has stalk exactly `𝔮` at
`x''` (`Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk`), and the stalk of the
closed subscheme cut out by an ideal sheaf is the quotient of the stalk by the stalk of that
ideal sheaf (`AlgebraicGeometry.Scheme.IdealSheafData.subschemeStalkRingEquiv`, which rests on
the surjectivity of the stalk map of a preimmersion together with the computation of its
kernel). What was missing is the composite, which the development has so far assembled by hand at
each use.

The identification is what lets a height-one prime `𝔮` of a two-dimensional local ring be read as
a divisor on the closure of the point it cuts out. In the situation of Stacks 0GU9, `W` is the
integral closed subscheme spanned by a point `x` of `δ`-dimension `k + 2`, the point `x''` has
`δ`-dimension `k`, and the height-one primes `𝔮` of `A = 𝒪_{W, x''}` correspond to the
intermediate points `x'` of `δ`-dimension `k + 1`
(`Stacks.Chow.heightOnePrimeEquivIntermediatePoint`). The summand of the tag's displayed sum at
`𝔮` is an order of vanishing taken in `A ⧸ 𝔮`, and the tag writes it as an order of vanishing in
`𝒪_{closure {x'}, x''}`. The two rings are identified below, so the two orders agree.

## What is carried

No further input is assumed. The general statements below hold for an arbitrary scheme, an
arbitrary point and an arbitrary prime of the local ring there: no Noetherian, integral or
dimension hypothesis appears, because none appears in the two statements being composed. The
specialization to the height-one correspondence carries the hypotheses of that correspondence,
namely integrality of the scheme and two-dimensionality of the local ring at `x''`.

## Main definitions

* `Stacks.Chow.fromSpecStalkClosurePoint` — the point `x''`, read as a point of the reduced
  closed subscheme spanned by `x' = X.fromSpecStalk x'' 𝔮`.
* `Stacks.Chow.quotStalkEquivClosureStalk` — **the identification**: `𝒪_{X, x''} ⧸ 𝔮` is the
  local ring of `closure {x'}` at `x''`.
* `Stacks.Chow.quotStalkEquivIntermediatePointStalk` — the same identification at a height-one
  prime, phrased through `Stacks.Chow.heightOnePrimeEquivIntermediatePoint`.

## Main results

* `Stacks.Chow.mem_closure_fromSpecStalk` — `x''` lies in the closure of the point that `𝔮`
  cuts out.
* `Stacks.Chow.stalkIdeal_integralComponentAt_fromSpecStalk` — the stalk at `x''` of the ideal
  sheaf of `closure {x'}` is `𝔮`.
* `Stacks.Chow.ord_quot_eq_ord_closureStalk` — the order of vanishing of a germ in `𝒪_{X,x''} ⧸ 𝔮`
  is its order of vanishing in `𝒪_{closure {x'}, x''}`.
* `Stacks.Chow.ord_quot_eq_ord_intermediatePointStalk` — the same at a height-one prime.

## References

* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The point below, read on the closure of the point above -/

/-- **The point `x''` lies in the closure of the point a prime of `𝒪_{X, x''}` cuts out.** The
range of `AlgebraicGeometry.Scheme.fromSpecStalk` at `x''` is the set of generizations of `x''`,
so the point attached to a prime specializes to `x''`. -/
theorem mem_closure_fromSpecStalk (x'' : X) (q : PrimeSpectrum (X.presheaf.stalk x'')) :
    x'' ∈ closure ({X.fromSpecStalk x'' q} : Set X) :=
  (specializes_fromSpecStalk x'' q).mem_closure

/-- **The point `x''`, read as a point of the reduced closed subscheme spanned by the point that
`𝔮` cuts out.** The two are the same datum; naming it is what lets the local ring and the residue
field of that subscheme at `x''` be spoken of. -/
def fromSpecStalkClosurePoint (x'' : X) (q : PrimeSpectrum (X.presheaf.stalk x'')) :
    (integralComponentAt (X.fromSpecStalk x'' q)).subscheme :=
  ⟨x'', mem_closure_fromSpecStalk x'' q⟩

@[simp] theorem subschemeι_fromSpecStalkClosurePoint (x'' : X)
    (q : PrimeSpectrum (X.presheaf.stalk x'')) :
    (integralComponentAt (X.fromSpecStalk x'' q)).subschemeι
      (fromSpecStalkClosurePoint x'' q) = x'' := rfl

/-! ### The ideal sheaf of the closure has stalk the prime -/

/-- **The ideal sheaf of `closure {x'}` has stalk exactly `𝔮` at `x''`**, for
`x' = X.fromSpecStalk x'' 𝔮`. This is
`Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk`, read through the definition of
`Stacks.Chow.integralComponentAt` as the vanishing ideal sheaf of the closure of a point. -/
theorem stalkIdeal_integralComponentAt_fromSpecStalk (x'' : X)
    (q : PrimeSpectrum (X.presheaf.stalk x'')) :
    (integralComponentAt (X.fromSpecStalk x'' q)).stalkIdeal x'' = q.asIdeal :=
  stalkIdeal_vanishingIdeal_closure_fromSpecStalk x'' q

/-! ### The identification -/

/-- **`𝒪_{X, x''} ⧸ 𝔮` is the local ring of `closure {x'}` at `x''`.** Let `x''` be a point of a
scheme `X`, let `𝔮` be a prime of `𝒪_{X, x''}` and let `x' = X.fromSpecStalk x'' 𝔮` be the point
of `X` it cuts out, so that `x''` lies in the closure of `x'`. Then the quotient of `𝒪_{X, x''}`
by `𝔮` is the local ring at `x''` of the reduced closed subscheme spanned by `x'`.

The isomorphism is the stalk map of the closed immersion `closure {x'} ⟶ X` at `x''`: that map is
surjective and its kernel is the stalk of the ideal sheaf, which is `𝔮`.

This identification is what reads a height-one prime of a two-dimensional local ring as a divisor
on the closure of the point it cuts out, and so what turns an order of vanishing along `A ⧸ 𝔮`
into an order of vanishing on that closure. -/
def quotStalkEquivClosureStalk (x'' : X) (q : PrimeSpectrum (X.presheaf.stalk x'')) :
    (X.presheaf.stalk x'' ⧸ q.asIdeal) ≃+*
      (integralComponentAt (X.fromSpecStalk x'' q)).subscheme.presheaf.stalk
        (fromSpecStalkClosurePoint x'' q) :=
  (Ideal.quotEquivOfEq (stalkIdeal_integralComponentAt_fromSpecStalk x'' q).symm).trans
    ((integralComponentAt (X.fromSpecStalk x'' q)).subschemeStalkRingEquiv
      (fromSpecStalkClosurePoint x'' q))

/-- The identification carries the class of a germ to the image of that germ under the stalk map
of the closed immersion, so it is the canonical one. -/
@[simp] theorem quotStalkEquivClosureStalk_mk (x'' : X)
    (q : PrimeSpectrum (X.presheaf.stalk x'')) (r : X.presheaf.stalk x'') :
    quotStalkEquivClosureStalk x'' q (Ideal.Quotient.mk q.asIdeal r) =
      (((integralComponentAt (X.fromSpecStalk x'' q)).subschemeι).stalkMap
        (fromSpecStalkClosurePoint x'' q)).hom r := rfl

/-! ### The order of vanishing across the identification -/

/-- **The order of vanishing of a germ in `𝒪_{X, x''} ⧸ 𝔮` is its order of vanishing in
`𝒪_{closure {x'}, x''}`.** This is `Stacks.Chow.ord_subschemeStalk` read at the ideal sheaf of
the closure of `x' = X.fromSpecStalk x'' 𝔮`, whose stalk at `x''` is `𝔮`. -/
theorem ord_quot_eq_ord_closureStalk (x'' : X) (q : PrimeSpectrum (X.presheaf.stalk x''))
    (r : X.presheaf.stalk x'') :
    Ring.ord (X.presheaf.stalk x'' ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal r) =
      Ring.ord ((integralComponentAt (X.fromSpecStalk x'' q)).subscheme.presheaf.stalk
          (fromSpecStalkClosurePoint x'' q))
        ((((integralComponentAt (X.fromSpecStalk x'' q)).subschemeι).stalkMap
          (fromSpecStalkClosurePoint x'' q)).hom r) :=
  Ring.ord_ringEquiv (quotStalkEquivClosureStalk x'' q) _

/-! ### At a height-one prime of the correspondence -/

variable {W : Scheme.{u}}

/-- The point `x''`, read as a point of the reduced closure of the intermediate point attached to
a height-one prime of `𝒪_{W, x''}`. -/
def intermediatePointClosurePoint (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    (integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subscheme :=
  fromSpecStalkClosurePoint x'' ⟨q.1, q.2.1⟩

/-- **The quotient-stalk identification at a height-one prime.** For a height-one prime `𝔮` of
`A = 𝒪_{W, x''}` with attached intermediate point `x'`, the quotient `A ⧸ 𝔮` is the local ring at
`x''` of the reduced closure of `x'`.

Composed with `Stacks.Chow.heightOnePrimeEquivIntermediatePoint`, this says that the ring in which
the summand of the displayed sum of Stacks 0GU9 at `𝔮` takes its order of vanishing is the local
ring `𝒪_{closure {x'}, x''}` in which the source takes it. -/
def quotStalkEquivIntermediatePointStalk (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    (W.presheaf.stalk x'' ⧸ q.1) ≃+*
      (integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subscheme.presheaf.stalk
        (intermediatePointClosurePoint x'' q) :=
  quotStalkEquivClosureStalk x'' ⟨q.1, q.2.1⟩

/-- The order of vanishing of a germ in `A ⧸ 𝔮` is its order of vanishing in the local ring of
the closure of the intermediate point attached to `𝔮`. -/
theorem ord_quot_eq_ord_intermediatePointStalk (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1})
    (r : W.presheaf.stalk x'') :
    Ring.ord (W.presheaf.stalk x'' ⧸ q.1) (Ideal.Quotient.mk q.1 r) =
      Ring.ord ((integralComponentAt
            (intermediatePointOfHeightOnePrime x'' q)).subscheme.presheaf.stalk
          (intermediatePointClosurePoint x'' q))
        ((((integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι).stalkMap
          (intermediatePointClosurePoint x'' q)).hom r) :=
  Ring.ord_ringEquiv (quotStalkEquivIntermediatePointStalk x'' q) _

end Stacks.Chow

end
