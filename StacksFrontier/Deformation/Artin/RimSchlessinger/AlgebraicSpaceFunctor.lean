module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm

/-!
# Condition (RS) for an algebraic space, in the functor form

Let `S` be a scheme contained in a big fppf site `B` and let `F` be an algebraic space over `S`.
By Stacks 07WQ its category fibred in groupoids, the algebraic stack
`AlgebraicGeometry.Stack.algebraicSpaceStack`, satisfies condition (RS) of Stacks 07WP; read
through the discrete fibres of that category, this says that `F` satisfies (RS) in the functor
form `Deformation.Artin.SatisfiesRSFunctor`.

## Main results

* `Deformation.Artin.satisfiesRSFunctor_of_isAlgebraicSpace`: an algebraic space satisfies
  (RS) in the functor form.

## References

* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space satisfies condition (RS).** For an algebraic space `F` over `S` and a
pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over `S` along a
closed immersion, every pair of points of `F` over `Y` and `X'` agreeing over `X` is the pair of
restrictions of exactly one point over `Y'`. This is Stacks 07WQ for the algebraic stack of `F`,
read through its discrete fibres. -/
theorem satisfiesRSFunctor_of_isAlgebraicSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) : SatisfiesRSFunctor B S hS F :=
  satisfiesRSFunctor_of_satisfiesRS
    (satisfiesRS_of_isAlgebraicStack B S hS (Stack.algebraicSpaceStack.{u, u} B S hS F hF))

end Deformation.Artin
