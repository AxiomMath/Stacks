module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidTransition

/-!
# Quasi-coherent modules on a quotient stack

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and `𝒳 = [U/R]` its quotient stack.
Stacks 06WT: the category of quasi-coherent `𝒪_𝒳`-modules is equivalent to the category
`QCoh(U, R, s, t, c)` of quasi-coherent modules on the groupoid (Stacks 0441).

The equivalence is the functor `ℱ ↦ (x^*ℱ|_{U_étale}, α)`
(`AlgebraicGeometry.Stack.quotientStackToGroupoid`), which is fully faithful
(`AlgebraicGeometry.Stack.fullyFaithfulQuotientStackToGroupoid`, from Stacks 076S) and
essentially surjective (the quasi-coherent module on `[U/R]` attached to `(𝒢, α)` by the
construction of the proof of Stacks 06WT maps to `(𝒢, α)`:
`AlgebraicGeometry.Stack.quotientStackToGroupoidObjIso`).

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackQuasicoherentEquivalence`: The equivalence between
  quasi-coherent `𝒪_𝒳`-modules on `[U/R]` and quasi-coherent modules on the groupoid.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The functor `quotientStackToGroupoid G` is full. -/
instance : (quotientStackToGroupoid G).Full := (fullyFaithfulQuotientStackToGroupoid G).full

/-- The functor `quotientStackToGroupoid G` is faithful. -/
instance : (quotientStackToGroupoid G).Faithful := (fullyFaithfulQuotientStackToGroupoid G).faithful

/-- The functor `quotientStackToGroupoid G` is an equivalence of categories. -/
instance : (quotientStackToGroupoid G).IsEquivalence where

/-- For a groupoid in algebraic spaces `(U, R, s, t, c)` over `S` with quotient stack `𝒳 = [U/R]`,
the category of quasi-coherent `𝒪_𝒳`-modules is equivalent to the category of quasi-coherent
modules on `(U, R, s, t, c)`, by `ℱ ↦ (x^*ℱ|_{U_étale}, α)`. -/
@[stacks 06WT]
def quotientStackQuasicoherentEquivalence :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
        (isFiberedInGroupoids_quotientStack G) ≌ Space.QuasicoherentModule C S hS G :=
  (quotientStackToGroupoid G).asEquivalence

end AlgebraicGeometry.Stack

end
