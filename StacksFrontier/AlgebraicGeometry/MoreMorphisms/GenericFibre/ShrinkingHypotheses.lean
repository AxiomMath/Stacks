module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The two missing inputs of the Tag 055A chain, packaged as hypotheses

Tags 0554 and 0559 of the Stacks Project are not yet available in the library, and both are
used by Tag 055A and hence by everything above it. This module states their conclusions as
`Prop`s so that the results depending on them can be stated with complete proofs, carrying
an explicit hypothesis instead of a tag.

## Main definitions

* `AlgebraicGeometry.IrreducibleComponentsLowerBoundAfterShrinking` is the conclusion of
  Stacks Tag 0554.
* `AlgebraicGeometry.GeometricallyIrreducibleAfterShrinking` is the conclusion of Stacks
  Tag 0559.

## Implementation notes

Both statements quantify over morphisms of schemes in a single fixed universe, which is how
every consumer uses them; neither is a typeclass, so the instance arguments of the Stacks
statements appear as explicit implications. Being of finite type is expressed by
`LocallyOfFiniteType` together with `QuasiCompact`.

## References

* [Stacks Project, Tag 0554](https://stacks.math.columbia.edu/tag/0554)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The conclusion of **Stacks Project, Tag 0554**: if the generic fibre of a finite type
morphism onto an irreducible base has `n` irreducible components, then every fibre over some
nonempty open subset of the base has at least `n` irreducible components. -/
def IrreducibleComponentsLowerBoundAfterShrinking : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), LocallyOfFiniteType f → QuasiCompact f →
    ∀ η : Y, IsGenericPoint η Set.univ → ∀ n : ℕ,
      (irreducibleComponents (f.fiber η)).ncard = n →
      ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
        ∀ y ∈ V, n ≤ (irreducibleComponents (f.fiber y)).ncard

/-- The conclusion of **Stacks Project, Tag 0559**: a finite type morphism onto an irreducible
base whose fibre over the generic point is geometrically irreducible has geometrically
irreducible fibres over a nonempty open subscheme of the base. -/
def GeometricallyIrreducibleAfterShrinking : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IrreducibleSpace Y → LocallyOfFiniteType f →
    QuasiCompact f → ∀ η : Y, IsGenericPoint η Set.univ →
      GeometricallyIrreducible (f.fiberToSpecResidueField η) →
      ∃ V : Y.Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V)

end AlgebraicGeometry

end
