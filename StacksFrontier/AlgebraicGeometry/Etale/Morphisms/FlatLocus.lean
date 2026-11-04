module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the flat locus over a locally Noetherian scheme

For a morphism locally of finite type over a locally Noetherian scheme, the relative flat locus
of a coherent module is open.

## Main results

* `AlgebraicGeometry.isOpen_setOf_coherent_flatOverAt`: the relative flat locus of a coherent
  module is open.

## Implementation notes

Flatness at a point is the stalkwise predicate `AlgebraicGeometry.IsFlatOverAt`.

## References

* [Stacks Project, Tag 0255](https://stacks.math.columbia.edu/tag/0255)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The relative flat locus of a coherent module over a locally Noetherian base is open. -/
@[ega "IV 11.1.1",
  sga "1 IV 6.10",
  ega "IV 11.1.6" "case C = B",
  ega "IV 11.3.1" "Noetherian case",
  sga "3 VIB 13.1" "(i) U open", sga "3 VIB 2.5" "special case"]
theorem isOpen_setOf_coherent_flatOverAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] :
    IsOpen {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have : F.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' F
  exact isOpen_setOf_flatOverAt f F

end AlgebraicGeometry
