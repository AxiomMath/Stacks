module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The input of the canonical factorization of a proper morphism

A proper morphism of schemes `f : X ⟶ S` factors canonically through the relative spectrum of
`f_* 𝒪_X`, the first map of the factorization being universally closed, quasi-compact,
quasi-separated and surjective. This file bundles the data of such a factorization problem: the
base, the source, and the proper morphism between them.

## Main definitions

* `AlgebraicGeometry.CanonicalSteinFactorizationSetup`: a proper morphism of schemes bundled with
  its base, its source and its properness.

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A proper morphism of schemes, bundled with its base and source. -/
structure CanonicalSteinFactorizationSetup where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The proper morphism to be factored. -/
  f : X ⟶ S
  /-- Properness of the morphism. -/
  [isProper_f : IsProper f]

attribute [instance] CanonicalSteinFactorizationSetup.isProper_f

end AlgebraicGeometry
