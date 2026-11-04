module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The standing situation for descent along an fppf morphism

Descent of properties of morphisms of schemes is stated repeatedly for a commutative triangle
`X ⟶ Y ⟶ S` in which the morphism `X ⟶ Y` is surjective, flat and locally of finite
presentation. This file packages that data.

## Main definitions

* `AlgebraicGeometry.CommonDescentSituation` bundles the three schemes, the three morphisms,
  the commutativity of the triangle, and the hypotheses on `X ⟶ Y`.

## Implementation notes

The equation `p = f ≫ q` is the categorical form of `p = q ∘ f`. The three properties of `f`
are instance fields, registered as instances below, so that results stated in this situation
can use the corresponding morphism-property instances directly.

## References

* [Stacks Project, Section 35.23](https://stacks.math.columbia.edu/tag/02KK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The standing commutative triangle `X ⟶ Y ⟶ S` for descent, with the
map `X ⟶ Y` surjective, flat, and locally of finite presentation. -/
structure CommonDescentSituation where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The intermediate scheme. -/
  Y : Scheme.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The morphism from the source to the intermediate scheme. -/
  f : X ⟶ Y
  /-- The morphism from the intermediate scheme to the base. -/
  q : Y ⟶ S
  /-- The structure morphism from the source to the base. -/
  p : X ⟶ S
  /-- The triangle commutes. -/
  p_eq : p = f ≫ q
  /-- The morphism `f` is surjective. -/
  [surjective_f : Surjective f]
  /-- The morphism `f` is flat. -/
  [flat_f : Flat f]
  /-- The morphism `f` is locally of finite presentation. -/
  [locallyOfFinitePresentation_f : LocallyOfFinitePresentation f]

attribute [instance] CommonDescentSituation.surjective_f
  CommonDescentSituation.flat_f
  CommonDescentSituation.locallyOfFinitePresentation_f

end AlgebraicGeometry
