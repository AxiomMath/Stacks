module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# J-2 schemes

A locally Noetherian scheme is J-2 if the regular locus of every scheme locally of finite type
over it is open. This is the scheme-theoretic counterpart of the ring-theoretic condition
`IsJ2`, and the condition under which the singular locus can be controlled after passing to
schemes of finite type over the base.

## Main definitions

* `AlgebraicGeometry.Scheme.IsJ2` is the J-2 condition for a locally Noetherian scheme.

## Main results

* `AlgebraicGeometry.Scheme.isJ2_iff` characterizes the J-2 condition by its defining universal
  property.
* `AlgebraicGeometry.Scheme.IsJ2.mk` and
  `AlgebraicGeometry.Scheme.IsJ2.isOpen_regularLocus` are the introduction and application
  interfaces for the condition.

## Implementation notes

Local Noetherianity is carried by a typeclass assumption. Schemes locally of finite type over
the base are expressed using `AlgebraicGeometry.LocallyOfFiniteType`, and their regular loci
using `AlgebraicGeometry.regularLocus`. The definition is exposed so its small defining
universal property is available across module boundaries; the accompanying lemmas let clients
introduce and apply the condition without explicitly unfolding it.

The leaf name matches the ring-theoretic `IsJ2`, so the definition lives in the `Scheme`
namespace: `X.IsJ2` reads, and there is no clash with the root-level ring condition.

## References

* [Stacks Project, Tag 07R3](https://stacks.math.columbia.edu/tag/07R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian scheme `X` is **J-2** if the regular locus of every scheme locally of
finite type over `X` is open. -/
@[stacks 07R3] public def IsJ2 (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [LocallyOfFiniteType f], IsOpen (regularLocus Y)

/-- The defining universal property of a J-2 scheme. -/
public theorem isJ2_iff (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [LocallyOfFiniteType f], IsOpen (regularLocus Y) :=
  Iff.rfl

/-- Introduce the J-2 condition by proving that all locally finite type schemes over the base
have open regular locus. -/
public theorem IsJ2.mk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [LocallyOfFiniteType f], IsOpen (regularLocus Y)) :
    IsJ2 X := h

/-- The regular locus of a scheme locally of finite type over a J-2 scheme is open. -/
public theorem IsJ2.isOpen_regularLocus {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsJ2 X) (f : Y ⟶ X) [LocallyOfFiniteType f] : IsOpen (regularLocus Y) :=
  hX Y f

end AlgebraicGeometry.Scheme
