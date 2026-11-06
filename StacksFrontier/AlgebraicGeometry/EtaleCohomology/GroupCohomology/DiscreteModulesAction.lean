module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Continuity of an action on a discrete module, for an arbitrary object of `Action`

`Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff` reads the continuity of the
action of a topological group `G` on a discrete `R`-module off the stabilizers, for the action
attached to a representation. The same criterion holds for an arbitrary object of
`CategoryTheory.Action (ModuleCat R) G`.

## Main results

* `Stacks.GroupCohomology.isContinuous_iff_forall_isOpen_stabilizer`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

variable {R : Type u} [Ring R] {G : Type v} [Group G] [TopologicalSpace G]

/-- **The action of `G` on a discrete `R`-module is continuous exactly when the stabilizers are
open**, for an arbitrary object of `CategoryTheory.Action (ModuleCat R) G`. This is the standard
reformulation of the continuity condition defining an `R`-`G`-module. -/
@[sga "4 IV 2.7.2" "special case"]
theorem isContinuous_iff_forall_isOpen_stabilizer [IsTopologicalGroup G]
    (V : Action (ModuleCat.{w} R) G) :
    V.IsContinuous ↔ ∀ x : V.V, IsOpen {g : G | (V.ρ g).asHom.hom x = x} :=
  continuousSMul_iff_stabilizer_isOpen

end Stacks.GroupCohomology
