module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Etale

/-!
# Étale-local properties of germs of schemes

A property of germs of schemes is étale local, respectively smooth local, if its truth is
unchanged along every étale, respectively smooth, morphism of germs. A property of morphisms
of germs is étale local on the source and target if it has the same truth value on the
horizontal arrows of every commutative square whose vertical arrows are étale.

## Main definitions

* `AlgebraicGeometry.GermOfScheme.IsEtaleLocal` expresses étale locality of a property of
  germs.
* `AlgebraicGeometry.GermOfScheme.IsSmoothLocal` expresses smooth locality of a property of
  germs.
* `AlgebraicGeometry.MorphismOfGerms.IsEtaleLocalOnSourceAndTarget` expresses étale locality
  on the source and target of a property of morphisms of germs.

## Main results

The field `AlgebraicGeometry.MorphismOfGerms.IsEtaleLocalOnSourceAndTarget.iff_of_etale_square`
applies the locality condition to an étale commutative square of germs.

## Implementation notes

Properties of germs are predicates on germs, and both locality conditions for them are
abbreviations, so their universal equivalences can be applied directly. The source germ of a
morphism is the first argument of `AlgebraicGeometry.MorphismOfGerms`. Properties of morphisms
are dependent predicates on morphisms of germs; composition of germs is written in
diagrammatic order, so the commutativity condition is `comp h' b = comp a h`. The structure
field is the direct API for applying the definition without unfolding it.

## References

* [Stacks Project, Tag 04N1](https://stacks.math.columbia.edu/tag/04N1)
* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- A property of germs is étale local if it has the same truth value at the source and target
of every étale morphism of germs. -/
@[stacks 04N1 "etale"]
abbrev GermOfScheme.IsEtaleLocal (P : GermOfScheme.{u} → Prop) : Prop :=
  ∀ {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S),
    MorphismOfGerms.IsEtale f → (P S ↔ P X)

/-- A property of germs is smooth local if it has the same truth value at the source and
target of every smooth morphism of germs. -/
@[stacks 04N1 "smooth"]
abbrev GermOfScheme.IsSmoothLocal (P : GermOfScheme.{u} → Prop) : Prop :=
  ∀ {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S),
    MorphismOfGerms.IsSmooth f → (P S ↔ P X)

/-- A property of morphisms of germs of schemes is étale local on the source and target if it
is invariant under commutative squares with étale vertical arrows. -/
@[stacks 04NB]
structure MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop) : Prop where
  /-- Étale maps on both sides of a commutative square preserve and reflect the property. -/
  iff_of_etale_square :
    ∀ {U' U V' V : GermOfScheme.{u}}
      (a : MorphismOfGerms U' U) (b : MorphismOfGerms V' V)
      (h' : MorphismOfGerms U' V') (h : MorphismOfGerms U V),
      MorphismOfGerms.IsEtale a → MorphismOfGerms.IsEtale b →
        MorphismOfGerms.comp h' b = MorphismOfGerms.comp a h → (Q h ↔ Q h')

end AlgebraicGeometry
