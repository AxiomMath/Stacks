module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A sheaf of commutative rings on a space, read as a ringed space

`AlgebraicGeometry.RingedSpace` bundles a space with a sheaf of commutative rings on it, and a
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat` is the same data. This module
is the passage between the two spellings.

They are not interchangeable to instance search, so results proved about one have to be
transported by hand; this is the transport. It is a `def` and not an `abbrev` deliberately:
`AlgebraicGeometry.RingedSpace` is a structure, and making the passage reducible would expose
its fields to unification wherever a ringed space is expected.

This module exists so that the passage is written once. It was defined identically in
`StacksFrontier/Topology/Sheaves/Modules/StalkKFlat.lean` and
`StacksFrontier/Topology/Sheaves/Modules/Flat/Stalk.lean`, which are import-independent, so neither
could host the canonical: importing either from the other costs 4 and 27 modules respectively,
while this module's only imports are Mathlib's.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}

/-- The ringed space whose underlying space is `X` and whose structure sheaf is `R`. -/
@[ega "0 4.1.1"]
def ringedSpaceOfSheaf
    (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u}) :
    AlgebraicGeometry.RingedSpace.{u, u} where
  carrier := X
  presheaf := R.obj
  IsSheaf := R.property

end AlgebraicGeometry.SheafOfModules

end
