module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Cartesian lifts and the chosen pullback of an object of a fibre

A *cartesian lift* of `f : V ⟶ U` at an object `x` over `U` is an object together with a
`p`-cartesian morphism to `x` over `f`. A prefibered functor supplies a *chosen* one for every `f`
and `x`, and reading its domain in the fibre over `V` gives `CategoryTheory.Functor.pullbackFiber`,
written `f^* x` throughout this directory. Everything Stacks 026F asks of a functor is phrased in
terms of these chosen pullbacks, so that no comparison isomorphism has to be quantified over.

## Main definitions

* `CategoryTheory.Functor.CartesianLift`, a cartesian lift of `f` at `x`;
* `CategoryTheory.Functor.pullbackFiber`, the chosen pullback, as an object of the fibre.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A cartesian lift of `f : V ⟶ U` at an object `x` of `𝒳` over `U`: an object `pt` together with
a `p`-cartesian morphism `pt ⟶ x` over `f`. -/
structure CartesianLift (p : 𝒳 ⥤ 𝒮) {U V : 𝒮} (f : V ⟶ U) (x : 𝒳) (_hx : p.obj x = U) where
  /-- The domain of the lift, an object of `𝒳` over `V`. -/
  pt : 𝒳
  /-- The lift itself. -/
  hom : pt ⟶ x
  /-- The lift is cartesian over `f`. -/
  isCartesian : p.IsCartesian f hom

/-- The chosen pullback of an object of the fibre over `U` along `f : V ⟶ U`, as an object of the
fibre over `V`. -/
@[implicit_reducible]
noncomputable def pullbackFiber (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {V U : 𝒮}
    (x : p.Fiber U) (f : V ⟶ U) : p.Fiber V :=
  ⟨IsPreFibered.pullbackObj x.2 f, IsPreFibered.pullbackObj_proj x.2 f⟩

end Functor

end CategoryTheory
