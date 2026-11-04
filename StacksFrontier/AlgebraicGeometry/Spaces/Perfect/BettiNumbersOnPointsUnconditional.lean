module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiConstructible
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BettiNumbersOnPoints

/-!
# Betti-number functions on the points of an algebraic space

Let `β : |X| → ℕ` be an `i`-th Betti-number function on the points of a presheaf `X` on the big
fppf site of `S`, in the sense of `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`: on
every étale chart it agrees with the `i`-th derived-fibre Betti function of a pseudo-coherent
complex on the charting scheme. Every level set of `β` is étale locally constructible, and if `X`
is an algebraic space then `β` is upper semicontinuous.

## Main results

* `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti.isEtaleLocallyConstructible_setOf_eq`:
  every level set of `β` is étale locally constructible (clause (3) of [Stacks, Tag 0D1Y]).
* `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti.upperSemicontinuous`: on an algebraic
  space, `β` is upper semicontinuous (clause (2) of [Stacks, Tag 0D1Y]).

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (β : points B S hS X → ℕ) (i : ℤ)

/-- Every level set of an `i`-th Betti-number function `β` on the points of `X`, in the sense of
`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`, is étale locally constructible. -/
theorem IsEtaleLocallyDerivedFibreBetti.isEtaleLocallyConstructible_setOf_eq
    (hβ : IsEtaleLocallyDerivedFibreBetti B S hS X β i)
    (n : ℕ) :
    IsEtaleLocallyConstructible B S hS X {x | β x = n} :=
  Space.isEtaleLocallyConstructible_setOf_eq B S hS X β i hβ
    (fun Z F hF m =>
      DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage Z F hF i m) n

/-- An `i`-th Betti-number function `β` on the points of an algebraic space `X`, in the sense of
`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`, is upper semicontinuous. -/
theorem IsEtaleLocallyDerivedFibreBetti.upperSemicontinuous
    (hX : IsAlgebraicSpace B S hS X)
    (hβ : IsEtaleLocallyDerivedFibreBetti B S hS X β i) :
    UpperSemicontinuous β :=
  Space.upperSemicontinuous_of_isEtaleLocallyDerivedFibreBetti B S hS X β i hX hβ
    fun Z F hF => DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti Z F hF i

end AlgebraicGeometry.Space

end
