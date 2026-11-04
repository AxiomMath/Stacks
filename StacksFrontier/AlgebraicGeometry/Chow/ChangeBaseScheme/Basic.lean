module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change for Chow homology

This file records a flat morphism between two base schemes for Chow homology, together with
the constant shift relating their dimension functions on the generic points of the fibres.

## Main definitions

* `Stacks.Chow.FlatBaseChangeSituation`: two Chow situations, a flat morphism between their
  bases, and an integer by which the two dimension functions differ on the generic points of
  irreducible components of its fibres.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
-/
@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-- A flat morphism between two bases for Chow homology whose dimension functions differ by a
fixed integer on the generic points of the irreducible components of every fibre. -/
@[stacks 0FVG]
structure FlatBaseChangeSituation where
  /-- The original base and its dimension function. -/
  base : ChowSituation.{u}
  /-- The base after base change and its dimension function. -/
  baseChange : ChowSituation.{u}
  /-- The base-change morphism. -/
  g : baseChange.S ⟶ base.S
  /-- The base-change morphism is flat. -/
  [flat : Flat g]
  /-- The constant shift between the two dimension functions. -/
  c : ℤ
  /-- On every generic point of an irreducible component of a fibre, the new dimension function
  is the old one plus `c`. -/
  dimensionFunction_eq_add : ∀ (s : base.S) (s' : genericPoints (g ⁻¹' {s} : Set baseChange.S)),
    baseChange.dimensionFunction s'.1.1 = base.dimensionFunction s + c

attribute [instance] FlatBaseChangeSituation.flat

end Stacks.Chow
