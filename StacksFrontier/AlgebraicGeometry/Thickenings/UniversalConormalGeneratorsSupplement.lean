module

public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
public import StacksFrontier.AlgebraicGeometry.Conormal.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
import all StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheafSupplement
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Additions to `UniversalConormalGenerators`

Further declarations about the module above, kept in their own module so that the base file is
unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace AlgebraicGeometry.RingedSpace

variable {Zr Xr : RingedSpace.{u, u}}

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- **`Stacks.ClosedImmersion.conormalSheafMap` read through the pullback comparison of its
square**: it is the inverse of `RingedSpaceModuleAdjunction.modulePullbackSquareIso`, followed by
the inverse image along the upper horizontal map of `Stacks.ClosedImmersion.idealSheafMap`.

This is `Stacks.ClosedImmersion.modulePullbackSquareIso_hom_app_comp_conormalSheafMap` with the
comparison moved to the other side.  It is the form in which the conormal map of a square is
recognised as the canonical map of a square in the sense of
`Stacks.CategoryTheory.square_map_comp`, and hence the form its composition law
`Stacks.ClosedImmersion.conormalSheafMap_comp` consumes. -/
theorem conormalSheafMap_eq (comm : i ≫ k = f ≫ j) :
    conormalSheafMap comm =
      (modulePullbackSquareIso f k i j comm).inv.app (idealSheaf j) ≫
        (modulePullback i).map (idealSheafMap comm) := by
  rw [← modulePullbackSquareIso_hom_app_comp_conormalSheafMap comm, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z Z' W W' : Scheme.{u}}

end Stacks.Immersion

namespace Stacks.Thickenings

open Stacks.ClosedImmersion Stacks.Immersion

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

end Stacks.Thickenings

end

