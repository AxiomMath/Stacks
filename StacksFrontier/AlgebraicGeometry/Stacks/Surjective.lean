module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points

/-!
# Surjective morphisms of algebraic stacks (Stacks 04ZS)

A morphism of algebraic stacks is surjective when its induced map on the underlying sets of
points is surjective.

The point sets and the map between them are those of Tag 04XG. Tag 04XL equips those sets with
their canonical topologies, but surjectivity is a property of the underlying function alone, so
it does not refer to a topology. The fibred-in-groupoids witness that the point map needs is
supplied by the algebraic-stack condition of Tag 026O, which is an existential over exactly that
witness; since it is a proposition, which witness is chosen does not matter.

This is an abbreviation, so the ordinary `Function.Surjective` API applies directly — in
particular its behaviour under composition.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.points` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`: the point set of an algebraic stack and
  the map induced by a 1-morphism, i.e. the notions of Tag 04XG with the fibredness witnesses
  read off the algebraic-stack condition.
* `AlgebraicGeometry.Stack.IsSurjective`: **Stacks 04ZS**, surjectivity of a morphism of
  algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_id`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`: functoriality of the map on
  points, and its invariance under 2-morphisms. Together they say that a 2-commutative square
  of algebraic stacks induces a commutative square of maps on points, which is what every
  permanence property of surjectivity is proved from.

## References

* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- The points of an algebraic stack over `S`: the points of **Stacks 04XG** of its underlying
category fibred in groupoids, formed with the fibred-in-groupoids witness read off the
algebraic-stack condition of Stacks 026O. -/
abbrev points (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Type (u + 1) :=
  Stack.points B S hS 𝒳.val.val (Classical.choose 𝒳.property)

/-- The map on points induced by a 1-morphism of algebraic stacks over `S`. -/
abbrev pointsMap {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    points B S hS 𝒳 → points B S hS 𝒴 :=
  Stack.pointsMap B S hS 𝒳.val.val
    (Classical.choose 𝒳.property) (Classical.choose 𝒴.property) f.hom.hom

/-- The map on points induced by the identity 1-morphism of an algebraic stack is the
identity. -/
theorem pointsMap_id (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    pointsMap B S hS (𝟙 𝒳) = id := by
  funext p
  induction p using Quotient.inductionOn with
  | h p => cases p; rfl

/-- The map on points of a composite of 1-morphisms of algebraic stacks is the composite of
the maps on points. -/
theorem pointsMap_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    pointsMap B S hS (f ≫ g) = pointsMap B S hS g ∘ pointsMap B S hS f := by
  funext p
  induction p using Quotient.inductionOn with
  | h p => cases p; rfl

/-- A 2-morphism of 1-morphisms of algebraic stacks does not change the induced map on
points; in particular a 2-commutative square induces a commutative square of maps on
points. -/
theorem pointsMap_eq_of_hom₂ {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴}
    (α : f ⟶ g) : pointsMap B S hS f = pointsMap B S hS g :=
  Stack.pointsMap_eq_of_basedNatTrans B S hS 𝒳.val.val
    (Classical.choose 𝒳.property) (Classical.choose 𝒴.property) α.hom.hom

end AlgebraicStacks

/-- **Stacks 04ZS.** A morphism of algebraic stacks is surjective if its map on points is
surjective. -/
@[stacks 04ZS]
abbrev IsSurjective {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  Function.Surjective (AlgebraicStacks.pointsMap B S hS f)

end AlgebraicGeometry.Stack

end
