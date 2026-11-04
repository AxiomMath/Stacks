module

public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Jacobson
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas

/-!
# Jacobson algebraic stacks

An algebraic stack over `S` is *Jacobson* when it admits a smooth surjective 1-morphism from a
scheme of the big fppf site over `S` whose underlying scheme is a Jacobson space. That is the
existential scheme-atlas criterion of Stacks 04YF at the property of being a Jacobson scheme, and
the Jacobson property of schemes is local in the smooth topology, so the four conditions of
Stacks 04YF agree and the notion is the one Stacks 04YG attaches to that property.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsJacobson`: the Jacobson condition on an algebraic
  stack.

## Main results

* `AlgebraicGeometry.jacobsonSpace_isLocal_smooth`: being a Jacobson scheme is local for the
  smooth precoverage.

## Implementation notes

Unlike the universally catenary property used for pseudo-catenary stacks, `JacobsonSpace` is
already a bare `CategoryTheory.ObjectProperty` on schemes, so no instance argument has to be
quantified over and local Noetherianity is not part of the asserted property.

## References

* [Stacks Project, Tag 0368](https://stacks.math.columbia.edu/tag/0368)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-- Being a Jacobson scheme is local for the smooth precoverage. -/
instance jacobsonSpace_isLocal_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => JacobsonSpace X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
  ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage

namespace Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` is *Jacobson* when it admits a smooth surjective 1-morphism from
a scheme of the big fppf site over `S` whose underlying scheme is a Jacobson space. -/
abbrev IsJacobson (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  Stack.HasPropertyOnSomeSchemeAtlas B S hS (fun X : Scheme.{u} => JacobsonSpace X) 𝒳

end Stack.AlgebraicStacks

end AlgebraicGeometry

end
