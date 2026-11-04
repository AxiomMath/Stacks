module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs

/-!
# The monoidal structure on modules over a sheaf of rings on a space, named

For a sheaf of commutative rings `Rc` on a topological space `X`, the monoidal, symmetric,
bilinear and closed structures on `Mod(O_X)` whose tensor product is `⊗_{O_X}`, stated at the
spelling `StructureSheafModules Rc` and named, so that a file in which instance search does not
reach them can register them with `attribute [local instance]`.

## Main definitions

* `Stacks.SheafOfModules.monoidalSpace'`, `Stacks.SheafOfModules.symmetricSpace'`,
  `Stacks.SheafOfModules.monoidalPreadditiveSpace'`, `Stacks.SheafOfModules.monoidalClosedSpace'`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The monoidal structure on `Mod(O_X)` whose tensor product is `⊗_{O_X}`. -/
local instance monoidalSpace' : MonoidalCategory (StructureSheafModules Rc) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is symmetric. -/
local instance symmetricSpace' : SymmetricCategory (StructureSheafModules Rc) :=
  SheafOfModules.symmetricCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is bilinear on morphisms. -/
local instance monoidalPreadditiveSpace' : MonoidalPreadditive (StructureSheafModules Rc) :=
  SheafOfModules.monoidalPreadditiveSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `Mod(O_X)` is monoidal closed. -/
local instance monoidalClosedSpace' : MonoidalClosed (StructureSheafModules Rc) :=
  SheafOfModules.monoidalClosedSheafTensor (J := Opens.grothendieckTopology X) Rc

end Stacks.SheafOfModules

end
