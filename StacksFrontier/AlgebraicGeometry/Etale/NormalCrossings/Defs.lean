module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.RingTheory.KrullDimension.SystemOfParameters.Defs

/-!
# Normal crossings divisors

An effective Cartier divisor on a locally Noetherian scheme has *strict normal crossings* when,
at every point of the divisor, its local equation is a product of a nonempty initial segment of
a regular system of parameters. It has *normal crossings* when every point of the divisor has an
étale neighbourhood on which the pullback of the divisor has strict normal crossings.

## Main definitions

* `Stacks.Divisors.IsStrictNormalCrossingsDivisor` is the strict normal crossings condition for
  an effective Cartier divisor.
* `Stacks.Divisors.IsNormalCrossingsDivisor` is the normal crossings condition.

## Implementation notes

A divisor is represented by its ideal sheaf data `Scheme.IdealSheafData`. Points of the divisor
are quantified as points of its associated subscheme, and the local ideal is the kernel of the
induced map from the ambient local ring to the divisor's local ring. A regular system of
parameters is a system of parameters whose entries generate the maximal ideal, and the defining
equation generates the local ideal as a principal ideal.

The pullback of a divisor along an étale chart is `Scheme.IdealSheafData.comap`. The chart's
locally Noetherian property is recorded as an explicit argument so that the strict normal
crossings predicate applies to the pullback; it follows mathematically from étaleness over the
locally Noetherian base.

Both predicates are abbreviations, so that clients can use their defining conditions directly.

## References

* [Stacks Project, Tag 0BI9](https://stacks.math.columbia.edu/tag/0BI9)
* [Stacks Project, Tag 0BSF](https://stacks.math.columbia.edu/tag/0BSF)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- An effective Cartier divisor locally cut out by a product of a nonempty initial segment of a
regular system of parameters. -/
@[stacks 0BI9,
  sga "5 I 3.1.5" "a) strict n.c."]
public abbrev IsStrictNormalCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) : Prop :=
  IsEffectiveCartierDivisor D ∧ ∀ y : D.subscheme,
    let x : X := D.subschemeι y; let R := X.presheaf.stalk x; IsRegularLocalRing R ∧
      ∃ (rs : List R) (r : ℕ), IsLocalRing.IsSystemOfParameters rs ∧
        Ideal.ofList rs = IsLocalRing.maximalIdeal R ∧ 1 ≤ r ∧ r ≤ rs.length ∧
        RingHom.ker (D.subschemeι.stalkMap y).hom = Ideal.span {(rs.take r).prod}

/-- An effective Cartier divisor which acquires strict normal crossings étale-locally at every
point of its support. -/
@[stacks 0BSF,
  sga "1 XIII 2.1.0" "absolute case", sga "5 I 3.1.5" "a) normal crossings"]
public abbrev IsNormalCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) : Prop :=
  IsEffectiveCartierDivisor D ∧ ∀ y : D.subscheme,
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (hU : IsLocallyNoetherian U), Etale f ∧
      (∃ q : U, f q = D.subschemeι y) ∧
      @IsStrictNormalCrossingsDivisor U hU (D.comap f)

end Stacks.Divisors

end
