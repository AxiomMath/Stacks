module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Restricting the scalars of a bilinear map of presheaves of modules

A bilinear map `M × N ⟶ P` of presheaves of `R'`-modules is bilinear over `R` after restricting
the scalars along a morphism of presheaves of rings `α : R ⟶ R'`: on sections the map is the same,
and `R` acts through `α`.

## Main definitions

* `Stacks.BilinearMap.restrictScalars`: the bilinear map with restricted scalars.
-/

@[expose] public section

open CategoryTheory PresheafOfModules Opposite

universe v u₁ u w₁ w₂ w₃

namespace Stacks.BilinearMap

variable {C : Type u₁} [Category.{v} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M : PresheafOfModules.{w₁} R'} {N : PresheafOfModules.{w₂} R'} {P : PresheafOfModules.{w₃} R'}

/-- **A bilinear map of presheaves of `R'`-modules, read over `R`** along `α : R ⟶ R'`: the same
map on sections, bilinear for the action of `R` through `α`. -/
noncomputable def restrictScalars (β : Stacks.BilinearMap M N P) :
    Stacks.BilinearMap ((PresheafOfModules.restrictScalars α).obj M)
      ((PresheafOfModules.restrictScalars α).obj N)
      ((PresheafOfModules.restrictScalars α).obj P) where
  app X := β.app X
  map_smul_left X r x y := β.map_smul_left X (α.app X r) x y
  map_smul_right X r x y := β.map_smul_right X (α.app X r) x y
  naturality f x y := β.naturality f x y

/-- The bilinear map with restricted scalars is the same map on sections. -/
@[simp]
theorem restrictScalars_app (β : Stacks.BilinearMap M N P) (X : Cᵒᵖ) :
    (restrictScalars α β).app X = β.app X :=
  rfl

end Stacks.BilinearMap
