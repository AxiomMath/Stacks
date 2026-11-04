module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Pullback of a finite type module along a morphism of schemes

Specialisation of the ringed-space statement
`AlgebraicGeometry.SheafOfModules.pullback_isFiniteType` (Stacks 01B6) to a morphism of
schemes, in the vocabulary of `AlgebraicGeometry.Scheme.Modules`.

This is the finite type counterpart of
`StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme`, which does the same for
quasi-coherence (Stacks 01BG); the two are almost always needed together, since the dévissage
arguments of Stacks 38.7 and 38.8 carry a module that is both quasi-coherent and of finite
type through a tower of pullbacks.

## Main results

* `Stacks.Modules.isFiniteType_pullback`, and its instance form
  `Stacks.Modules.instIsFiniteTypePullbackObj`: the pullback of a finite type module along an
  *arbitrary* morphism of schemes is of finite type.

## Implementation notes

No mathematics happens here: for a morphism of schemes `f : X ⟶ Y` the comparison between the
scheme-level and the ringed-space-level pullback is definitional, exactly as described in the
implementation notes of `QuasicoherentPullbackScheme`. The point of the module is that the
ringed-space instance is stated at the type `_root_.Modules Y.toRingedSpace`, which is a
structure copy of `AlgebraicGeometry.Scheme.Modules` with its own category instance, so the
ringed-space instance is *not* the instance that a goal about `Scheme.Modules.pullback f`
asks for. Without the instance below, every caller has to supply the finite type hypothesis by
an explicit `@`-application, which is both noisy and expensive to elaborate.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 01B6 for schemes.** The pullback of a finite type module along an arbitrary
morphism of schemes is of finite type. This is the specialisation of
`AlgebraicGeometry.SheafOfModules.pullback_isFiniteType` along the definitional
identification of `Scheme.Modules.pullback f` with pullback on the underlying ringed
spaces. -/
lemma isFiniteType_pullback (M : Y.Modules) (hM : M.IsFiniteType) :
    ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
  @AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
    X.toLocallyRingedSpace.toRingedSpace Y.toLocallyRingedSpace.toRingedSpace
    f.toLRSHom.toShHom M hM

/-- **Stacks 01B6 for schemes**, in instance form, so that finite type of a pullback is found
by instance search. -/
instance instIsFiniteTypePullbackObj (M : Y.Modules) [h : M.IsFiniteType] :
    ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
  isFiniteType_pullback f M h

end Stacks.Modules

end
