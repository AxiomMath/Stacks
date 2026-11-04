module

public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The pullback of a flat sheaf of modules is flat

Let `f : X ⟶ Y` be a morphism of ringed spaces and `F` a flat sheaf of `𝒪_Y`-modules.  Then
`f^*F` is a flat sheaf of `𝒪_X`-modules.  No hypothesis on `f` is needed.

Flatness of a sheaf of modules on a ringed space is stalkwise (Stacks 05NE,
`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`), the stalk of `f^*F` at `x` is the base
change `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} F_{f x}` (Stacks 0098,
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`), and a base change of a flat
module is flat.

## Main results

* `RingedSpaceModuleAdjunction.isFlat_modulePullback`: `f^*F` is flat when `F` is.

## Implementation notes

The stalk formula is stated over Mathlib's module structure on the stalk of a presheaf of modules,
which is also the one the stalkwise criterion is stated over (both are the instance of
`Mathlib.Algebra.Category.ModuleCat.Stalk`), so the linear equivalence transports flatness
directly.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction

/-- **The pullback of a flat sheaf of modules along any morphism of ringed spaces is flat.** -/
theorem isFlat_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((modulePullback f).obj F) := by
  have hF := (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Y.sheaf F).1 hF
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf _).2 (fun x => ?_)
  obtain ⟨e, -⟩ := exists_modulePullbackStalkLinearEquiv f F x
  -- The algebra and module structures are read off `e` and `hF` by unification (the `(_)`
  -- holes), not by instance search: several definitionally equal module structures on a stalk
  -- are in scope, and instance search would pick one independently of the hypotheses.
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ (_) _ (_)
    (@Module.Flat.baseChange _ _ _ _ _ (_) _ (_) (hF _)) e

end RingedSpaceModuleAdjunction

end
