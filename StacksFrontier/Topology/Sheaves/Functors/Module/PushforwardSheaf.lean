module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008W — pushforward of a sheaf of modules is a sheaf of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces, let `𝒪` be a sheaf of rings on `X`,
and let `ℱ` be a sheaf of `𝒪`-modules. Stacks 008W says the pushforward `f_*ℱ` of tag 008S is
a sheaf of `f_*𝒪`-modules.

Mathlib states this at the level of sites. Sheaves on `X : TopCat` are sheaves on `Opens X`
with `Opens.grothendieckTopology X`, for which `Opens.map f : Opens Y ⥤ Opens X` is continuous;
`CategoryTheory.Functor.sheafPushforwardContinuous` at that functor is the pushforward `f_*𝒪`
of the sheaf of rings, and `SheafOfModules.pushforward` is the pushforward functor on sheaves of
modules, whose values are sheaves of `f_*𝒪`-modules by construction.
-/

@[expose] public section

-- The former @[stacks 008W] theorem was the sheaf condition already carried by the values of
-- `SheafOfModules.pushforward`, the functor being that Mathlib functor at the identity.
add_to_stacks 008W "the pushforward `f_*𝒪` of the sheaf of rings, along the continuous functor
  `Opens.map f`" CategoryTheory.Functor.sheafPushforwardContinuous
add_to_stacks 008W "pushforward of sheaves of modules: `f_*ℱ` is a sheaf of `f_*𝒪`-modules,
  functorially in `ℱ`" SheafOfModules.pushforward
