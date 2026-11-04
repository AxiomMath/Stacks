module

public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# Additions to `PullbackComp`

Further declarations supplementing the module above, kept in their own module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y Z : RingedSpace.{u, u}}

/-- **The left unit law of the pullback pseudofunctor**, read on the backward maps: the inverse of
the composition isomorphism at `𝟙 X ≫ g` is the forward map of `modulePullbackId`, taken at the
pullback of `M` along `g`. This is `CategoryTheory.SheafOfModules.pullback_comp_id` at the
structure-sheaf map of `g`; its forward form is
`AlgebraicGeometry.RingedSpaceThickening.modulePullbackComp_id_hom_app`. -/
theorem modulePullbackComp_id_left_inv_app (g : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullbackComp (𝟙 X) g).inv.app M =
      (modulePullbackId X).hom.app ((modulePullback g).obj M) :=
  congrArg Iso.inv
    (Iso.ext (congrArg (fun e => e.inv.app M)
        (SheafOfModules.pullback_comp_id (φ := structureSheafHom g))) :
      (modulePullbackComp (𝟙 X) g).app M =
        ((modulePullbackId X).app ((modulePullback g).obj M)).symm)

/-- **The right unit law of the pullback pseudofunctor.** At the composite `f ≫ 𝟙 Y` the pullback
composition isomorphism is the pullback along `f` of the identification of pullback along `𝟙 Y`
with the identity functor.

This is `CategoryTheory.SheafOfModules.pullback_id_comp` at the structure-sheaf map of `f`, with
the whiskering and the unitor of that equation of isomorphisms read at a component. -/
theorem modulePullbackComp_id_right_hom_app (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullbackComp f (𝟙 Y)).hom.app M =
      (modulePullback f).map ((modulePullbackId Y).inv.app M) :=
  congrArg (fun e => e.inv.app M)
    (SheafOfModules.pullback_id_comp (φ := structureSheafHom f))

end RingedSpaceModuleAdjunction

end

