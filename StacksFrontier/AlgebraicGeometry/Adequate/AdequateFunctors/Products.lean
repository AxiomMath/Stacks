module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Factors
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.FamilyToProduct
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Equivalence

/-!
# Adequate functors over finite products of rings

An adequate module-valued functor over a finite product of commutative rings is the same as a
family of adequate module-valued functors over the factors.

## Main definitions

* `AdequateFunctor.piAlgHom` is the coordinatewise map between products of algebras.
* `AdequateFunctor.ProductEquivalenceSpecification` records a componentwise comparison
  natural in both the algebra and the factor functors.

## Main results

* `AdequateFunctor.adequateFunctorProductEquivalence` gives the equivalence of categories
  of adequate functors, together with its componentwise evaluation on products of algebras.

## Implementation notes

The equivalence is categorical, retaining morphisms and their naturality. Its inverse is equipped
with componentwise module isomorphisms natural both in product algebras and in the family of factor
functors. For a finite family, the product of modules is also their coproduct as additive groups.
The full subcategories use the adequacy predicate of Tag 06UT. Indexing by `Fin n` includes the
empty product.

## Contents

* `StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Factors`: algebras and
  modules over the factors of a finite product of rings.
* `StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.FamilyToProduct`: assembling
  a family of functors over the factors into one adequate functor over the product.
* `StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Equivalence`: the unit,
  counit equivalence of categories.

## References

* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
-/
