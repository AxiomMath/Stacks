module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# Discrete fibres of étale morphisms

The scheme-theoretic fibres of an étale morphism of schemes have discrete underlying
topological spaces.

## Main results

* `AlgebraicGeometry.discreteTopology_fiber` states that every fibre of an étale morphism is
  discrete.

## Implementation notes

Fibres are represented by Mathlib's scheme-theoretic fibre `Scheme.Hom.fiber`, and discreteness
of its underlying space is expressed by the `DiscreteTopology` typeclass. The input is that an
étale morphism is locally quasi-finite, which gives discreteness of the set-theoretic preimage
of a point; transporting along the homeomorphism between that preimage and the scheme-theoretic
fibre gives the statement.

## References

* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Every scheme-theoretic fibre of an étale morphism is a discrete space. -/
@[stacks 03II "etale_discrete_fibres"]
theorem discreteTopology_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] (s : S) : DiscreteTopology (f.fiber s) :=
  (f.fiberHomeo s).discreteTopology_iff.mpr
    (@Scheme.Hom.isDiscrete_preimage_singleton _ _ f
      (locallyQuasiFinite_of_etale f).2 s).to_subtype

end AlgebraicGeometry
