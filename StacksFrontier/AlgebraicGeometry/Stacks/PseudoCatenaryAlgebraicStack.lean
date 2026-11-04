module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas

/-!
# Pseudo-catenary algebraic stacks (Stacks 0DRU)

**Stacks 0DRU** calls a locally Noetherian algebraic stack over `S` *pseudo-catenary* when it
admits a smooth surjective 1-morphism from a scheme of the big fppf site over `S` whose
underlying scheme is universally catenary.

That is the existential scheme-atlas criterion of **Stacks 04YF** at the property of being a
universally catenary scheme, so it is stated here as
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` at that property rather than as a second
existential of its own.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsPseudoCatenary`: **Stacks 0DRU**.

## Implementation notes

`AlgebraicGeometry.Scheme.IsUniversallyCatenary` (**Stacks 02J8**) is a predicate on a scheme
carrying `AlgebraicGeometry.IsLocallyNoetherian` as an instance argument, while the property
asked of an atlas by Stacks 04YF is a bare `CategoryTheory.ObjectProperty`. The property used
here therefore quantifies over that instance, so that local Noetherianity of the atlas is part of
the asserted property rather than a side condition on the stack.

Local Noetherianity of the stack itself is not a further conjunct: it is the same Stacks 04YF
criterion at `AlgebraicGeometry.IsLocallyNoetherian`, which this condition implies, since the
atlas it produces is locally Noetherian. That is the reading under which the
`@[stacks 0DQI]` statements take local Noetherianity of an algebraic stack as a hypothesis.

## References

* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 0DRU](https://stacks.math.columbia.edu/tag/0DRU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DRU.** An algebraic stack over `S` is *pseudo-catenary* when it admits a smooth
surjective 1-morphism from a scheme of the big fppf site over `S` whose underlying scheme is
locally Noetherian and universally catenary. -/
@[stacks 0DRU]
abbrev IsPseudoCatenary (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  Stack.HasPropertyOnSomeSchemeAtlas B S hS
    (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @Scheme.IsUniversallyCatenary X h) 𝒳

end AlgebraicGeometry.Stack.AlgebraicStacks

end
