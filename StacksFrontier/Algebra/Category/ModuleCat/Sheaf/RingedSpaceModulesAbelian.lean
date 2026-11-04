module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect

/-!
# Sheaves of modules on a ringed space form an abelian category

For a ringed space `Z` whose underlying space and structure sheaf live in one universe `u`, the
category of sheaves of `𝒪_Z`-modules is abelian.

## Main results

* `Stacks.AssociatedSheaf.abelianModulesRingSheaf`: `Mod(𝒪_Z)` is abelian, at the spelling
  `SheafOfModules (structureSheafRing Z)`.

## Implementation notes

The sheafification of abelian presheaves on the opens of `Z` with values in `AddCommGrpCat.{u}`
and the identification of its weak equivalences with the locally bijective maps are
`Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens` and
`Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens`. The instance is not
global; a consumer activates it with `attribute [local instance]`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AssociatedSheaf

attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

/-- Sheaves of modules on a ringed space form an abelian category, at the spelling
`SheafOfModules (structureSheafRing Z)`. -/
@[instance_reducible] def abelianModulesRingSheaf (Z : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (structureSheafRing Z)) :=
  _root_.SheafOfModules.instAbelian _

end Stacks.AssociatedSheaf

end
