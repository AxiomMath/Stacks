module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension

/-!
# The relative Poincaré duality situation

The standing data of relative Poincaré duality for de Rham cohomology: a proper smooth morphism
over a quasi-compact, quasi-separated base all of whose fibres are nonempty and equidimensional
of one fixed dimension.

## Main definitions

* `AlgebraicGeometry.RelativeDualitySituation` bundles the standing data and hypotheses of
  relative Poincaré duality.

## References

* [Stacks Project, Tag 0G8G](https://stacks.math.columbia.edu/tag/0G8G)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A proper smooth morphism over a quasi-compact quasi-separated scheme, with all fibres
nonempty and equidimensional of dimension `n`. -/
@[stacks 0G8G]
structure RelativeDualitySituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The morphism. -/
  f : X ⟶ S
  /-- The common dimension of its fibres. -/
  n : ℕ
  /-- The base is quasi-compact. -/
  [compactSpace : CompactSpace S]
  /-- The base is quasi-separated. -/
  [quasiSeparatedSpace : QuasiSeparatedSpace S]
  /-- The morphism is proper. -/
  [isProper : IsProper f]
  /-- The morphism is smooth. -/
  [smooth : Smooth f]
  /-- Every fibre has a point. -/
  fiber_nonempty : ∀ s : S, Nonempty (f.fiber s)
  /-- Each fibre is equidimensional of the specified dimension. -/
  relativeDimension : RelativeDimension f n

namespace RelativeDualitySituation

attribute [instance] compactSpace quasiSeparatedSpace isProper smooth

end RelativeDualitySituation

end AlgebraicGeometry
