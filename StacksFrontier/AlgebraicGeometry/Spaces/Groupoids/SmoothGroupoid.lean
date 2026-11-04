module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Smooth groupoids in algebraic spaces (Stacks 04TH)

Let `B` be an algebraic space over a scheme `S` of a big fppf site. A groupoid
`(U, R, s, t, c)` in algebraic spaces over `B`, in the sense of Stacks 043W, is called
*smooth* when its source and target morphisms `s, t : R ⟶ U` are smooth morphisms of
algebraic spaces.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth`: **Stacks 04TH**.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth.source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth.target` name the two conjuncts.

## Implementation notes

The definition is an abbreviation for the conjunction of the two smoothness conditions, so a
consumer may destructure it, or supply it, as a plain `And`; the two accessors below are
provided only so that the conjuncts can be named at a use site.

As the source's own footnote warns, the terminology is potentially misleading: smoothness of a
groupoid in this sense says nothing about smoothness of its quotient stack `[U/R]` over
anything. The name is nevertheless kept, since it is the one the source's theory of
presentations (Stacks 04TI) is stated in.

Smoothness is imposed on the source and target morphisms *of algebraic spaces*, through
`AlgebraicGeometry.Space.IsSmooth` (Stacks 03ZC), and not on the underlying morphisms of
presheaves; the structure morphisms to `B` and the composition play no part.

## References

* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z : AlgebraicSpaces B S hS}

/-- **Stacks 04TH.** A groupoid `(U, R, s, t, c)` in algebraic spaces over `B` is *smooth* when
both its source and its target morphism `R ⟶ U` are smooth morphisms of algebraic spaces.

Despite the name this does not say that the quotient stack `[U/R]` is smooth over anything. -/
@[stacks 04TH]
abbrev IsSmooth (G : GroupoidInAlgebraicSpaces B S hS Z) : Prop :=
  Space.IsSmooth B S hS G.source.hom ∧ Space.IsSmooth B S hS G.target.hom

/-- The source morphism of a smooth groupoid in algebraic spaces is smooth. -/
theorem IsSmooth.source {G : GroupoidInAlgebraicSpaces B S hS Z} (hG : IsSmooth B S hS G) :
    Space.IsSmooth B S hS G.source.hom :=
  hG.1

/-- The target morphism of a smooth groupoid in algebraic spaces is smooth. -/
theorem IsSmooth.target {G : GroupoidInAlgebraicSpaces B S hS Z} (hG : IsSmooth B S hS G) :
    Space.IsSmooth B S hS G.target.hom :=
  hG.2

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
