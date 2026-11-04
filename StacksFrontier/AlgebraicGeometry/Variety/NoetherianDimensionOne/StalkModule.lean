module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# Stalks of a sheaf of modules on a scheme

The stalk of a sheaf of `𝒪_X`-modules at a point is a module over the stalk of `𝒪_X` there, in
both the `Scheme.presheaf` and the `Scheme.toRingedSpace` spellings of the two stalks, and the
germ map is semilinear for it.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TopCat

universe u

namespace AlgebraicGeometry.NoetherianDimensionOne

/-- The stalk of a sheaf of modules on a scheme is a module over the stalk of the structure
sheaf. -/
noncomputable instance schemeStalkModule (X : Scheme.{u})
    (M : SheafOfModules.{u} X.ringCatSheaf) (x : X) :
    Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

/-- The same module structure on a stalk, with both carriers spelled through
`Scheme.toRingedSpace`. `Scheme.toRingedSpace` is a plain `def`, so instance search does not
connect the two spellings on its own. -/
noncomputable instance schemeStalkModuleRingedSpace (X : Scheme.{u})
    (M : SheafOfModules.{u} X.ringCatSheaf) (x : X) :
    Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace M.val x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

end AlgebraicGeometry.NoetherianDimensionOne

end
