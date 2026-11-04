module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The Cohen–Macaulay curve situation

A proper one-dimensional scheme over a field whose only global regular functions are the
constants from the base field. This is the standing situation under which the vanishing
results for curves are proved.

## Main definitions

* `AlgebraicGeometry.CohenMacaulayCurveSituation` is the standing situation of a proper curve
  over a field with global sections equal to that field.

## Implementation notes

The equality `H⁰(X, 𝒪_X) = k` is represented canonically: the ring homomorphism from `k` to the
global sections induced by the structure morphism is an isomorphism. The standard
identification of the global sections of `Spec k` with `k` is included explicitly in this map.

## References

* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B5D.** The standing situation of a proper one-dimensional scheme
over a field whose canonical ring of global sections is the base field. -/
@[stacks 0B5D] structure CohenMacaulayCurveSituation where
  /-- The base field. -/
  k : Type u
  /-- The field structure on the base. -/
  [field : Field k]
  /-- The proper curve. -/
  X : Scheme.{u}
  /-- The structure morphism to the spectrum of the base field. -/
  f : X ⟶ Spec (.of k)
  /-- The structure morphism is proper. -/
  [proper : IsProper f]
  /-- The scheme has dimension one. -/
  dimension_one : topologicalKrullDim X = 1
  /-- The canonical homomorphism from the base field to the ring of global sections is an
  isomorphism. -/
  [isIso_globalSections : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

open CohenMacaulayCurveSituation in attribute [instance] field proper isIso_globalSections

end AlgebraicGeometry
