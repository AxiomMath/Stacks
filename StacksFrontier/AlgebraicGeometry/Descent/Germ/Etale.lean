module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Basic

/-!
# Étale and smooth morphisms of germs of schemes

A morphism of germs of schemes is étale, respectively smooth, when it has a representative on
an open neighbourhood which is an étale, respectively smooth, morphism of schemes.

## Main definitions

* `AlgebraicGeometry.MorphismOfGerms.IsEtale` says that a morphism of germs has an étale
  representative.
* `AlgebraicGeometry.MorphismOfGerms.IsSmooth` says that a morphism of germs has a smooth
  representative.

## Main results

There are no results beyond the definitions.

## Implementation notes

Both predicates are existential properties of a representative. They are abbreviations so
that clients can use the representative directly. Étaleness and smoothness of the representing
scheme morphism are Mathlib's `AlgebraicGeometry.Etale` and `AlgebraicGeometry.Smooth`
classes.

## References

* [Stacks Project, Tag 04QS](https://stacks.math.columbia.edu/tag/04QS)
-/

@[expose] public section

namespace AlgebraicGeometry

namespace MorphismOfGerms

universe u

/-- A morphism of germs is étale if it is represented on some open neighbourhood by an étale
morphism of schemes. -/
@[stacks 04QS "etale"]
abbrev IsEtale {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : Representative X S, mk g = f ∧ AlgebraicGeometry.Etale g.hom

/-- A morphism of germs is smooth if it is represented on some open neighbourhood by a smooth
morphism of schemes. -/
@[stacks 04QS "smooth"]
abbrev IsSmooth {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : Representative X S, mk g = f ∧ AlgebraicGeometry.Smooth g.hom

end MorphismOfGerms

end AlgebraicGeometry
