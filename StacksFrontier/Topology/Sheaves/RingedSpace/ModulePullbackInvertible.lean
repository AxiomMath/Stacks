module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The pullback of an invertible module is invertible

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `L` be an invertible sheaf of
`𝒪_Y`-modules in the sense of Tag 01CS: tensoring by `L` is an autoequivalence of
`Mod(𝒪_Y)`. Then `f^* L` is an invertible sheaf of `𝒪_X`-modules.

## Main results

* `RingedSpaceModuleAdjunction.modulePullback_isInvertible`: invertibility is preserved
  by the pullback along any morphism of ringed spaces.
* `RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme`: the same statement
  for a morphism of schemes, in the spelling that the sheaves of modules on a scheme use.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (isInvertible_iff_exists_tensor_iso_unit
  isInvertible_of_tensor_iso_unit)

universe u

namespace RingedSpaceModuleAdjunction

/-- The pullback of an invertible module is invertible: if tensoring by `L` is an
autoequivalence of `Mod(𝒪_Y)`, then tensoring by `f^* L` is an autoequivalence of `Mod(𝒪_X)`. -/
@[stacks 0B8L]
theorem modulePullback_isInvertible {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf (structureSheafRing
        Y).property))
    [IsInvertible Y.presheaf (structureSheafRing Y).property L] :
    IsInvertible X.presheaf (structureSheafRing X).property
      ((RingedSpaceModuleAdjunction.modulePullback f).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ :=
    (isInvertible_iff_exists_tensor_iso_unit Y.presheaf (structureSheafRing Y).property L).mp ‹_›
  exact isInvertible_of_tensor_iso_unit X.presheaf (structureSheafRing X).property
    (N := (RingedSpaceModuleAdjunction.modulePullback f).obj N)
    (((Stacks.RingedSpace.comparisonBifunctorIso f).app (L, N)).symm ≪≫
    (Stacks.RingedSpace.pullbackFunctor f).mapIso e ≪≫ modulePullbackUnitIso f)

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
theorem modulePullback_isInvertible_scheme {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    IsInvertible X.presheaf X.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L) :=
  modulePullback_isInvertible f.toLRSHom.toShHom L

end RingedSpaceModuleAdjunction

end
