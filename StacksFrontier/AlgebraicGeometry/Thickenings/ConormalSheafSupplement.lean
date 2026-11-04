module

public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import all StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Additions to `ConormalSheaf`

Further declarations about the module above, kept in their own module so that the base file is
unchanged.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction 

universe u

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- **`Stacks.ClosedImmersion.pullbackCompIso` written out**, as the composition comparison of
[Stacks Project, Tag 0097] (2) on each side and the transport along the commutativity of the
square in between. -/
theorem pullbackCompIso_hom (comm : i ≫ k = f ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing W')) :
    (pullbackCompIso comm M).hom =
      (modulePullbackComp f j).inv.app M ≫
        (modulePullbackCongr comm.symm).hom.app M ≫ (modulePullbackComp i k).hom.app M := by
  rw [pullbackCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]

end Stacks.ClosedImmersion

namespace Stacks.Thickenings

open Stacks.ClosedImmersion

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

end Stacks.Thickenings

end

