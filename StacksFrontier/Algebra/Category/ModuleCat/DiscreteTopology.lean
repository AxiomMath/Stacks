module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Modules as discrete topological spaces

A module carries the discrete topology, and a group action on it is continuous for that
topology. Both facts are `scoped instance`s: they are needed wherever continuous cohomology
of discrete modules is formed, but a global `HasForget₂ (ModuleCat R) TopCat` would impose the
discrete topology on every module in the library, so they are offered under a namespace instead
of installed.

## Main definitions

* `Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat`: the forgetful functor from modules
  to topological spaces that gives a module the discrete topology.
* `Stacks.DiscreteModuleTopology.actionDiscreteTopology`: the underlying space of a module with
  a group action is discrete.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.DiscreteModuleTopology

/-- Modules as topological spaces, each with the discrete topology. -/
scoped instance hasForget₂ModuleCatTopCat (R : Type u) [Ring R] :
    HasForget₂ (ModuleCat.{w} R) TopCat.{w} :=
  { forget₂ := forget (ModuleCat.{w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

attribute [local instance] hasForget₂ModuleCatTopCat

/-- The space underlying a module with a group action is discrete. -/
scoped instance actionDiscreteTopology (R : Type u) [Ring R] (G : Type v) [Group G]
    [TopologicalSpace G] (X : Action (ModuleCat.{w} R) G) :
    DiscreteTopology ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X) := ⟨rfl⟩

end Stacks.DiscreteModuleTopology

end
