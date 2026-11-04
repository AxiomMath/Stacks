module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of a module of finite type

The pullback of a sheaf of modules of finite type along a morphism of schemes is again of finite
type. This specializes `AlgebraicGeometry.SheafOfModules.pullback_isFiniteType`, which holds for
every morphism of ringed spaces.

## Main results

* `AlgebraicGeometry.Scheme.Modules.instIsFiniteTypePullbackObj`: the pullback of a module of
  finite type along a morphism of schemes is of finite type.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

universe u

add_to_stacks 056J "pullback_finite_type"
  AlgebraicGeometry.SheafOfModules.pullback_isFiniteType

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a module of finite type along a morphism of schemes is of finite type. -/
instance instIsFiniteTypePullbackObj {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsFiniteType] : ((Scheme.Modules.pullback f).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom F

end AlgebraicGeometry.Scheme.Modules

end
