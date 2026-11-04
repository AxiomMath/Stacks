module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# h coverings

A family of morphisms of schemes is an h covering when every member is locally of finite
presentation and the family is a ph covering.

## Main definitions

* `AlgebraicGeometry.IsHCovering`: the predicate that a family of morphisms of schemes is an
  h covering.

## References

* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A family `{X i ⟶ T}` of morphisms of schemes is an *h covering* when
every member is locally of finite presentation and the family is a ph covering. -/
@[stacks 0ETS]
public abbrev IsHCovering {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) : Prop :=
  (∀ i, LocallyOfFinitePresentation (f i)) ∧ IsPHCovering X f

end AlgebraicGeometry
