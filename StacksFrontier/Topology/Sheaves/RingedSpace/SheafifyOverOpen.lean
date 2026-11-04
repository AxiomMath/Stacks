module

public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Sheafification on the slices of the open-cover site of a ringed space

For a ringed space `X` and an open `W`, the slice `(Opens.grothendieckTopology X).over W` of the
open-cover site has sheafification of presheaves of abelian groups, and its weak equivalences
of such presheaves are the locally bijective morphisms.  Both are scoped instances.

## Main definitions

* `Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen`
* `Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen`
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Topology.RingedSpaceSheafifyOpens

/-- Abelian sheaves on the slice of the site of opens of a ringed space over an open have a
sheafification. -/
scoped instance hasSheafifyOverOpen {X : RingedSpace.{u, u}} (W : Opens X.carrier) :
    HasSheafify ((Opens.grothendieckTopology X.carrier).over W) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat ((Opens.grothendieckTopology X.carrier).over W)

/-- On a slice of the site of opens of a ringed space the weak equivalences of abelian sheaves
are the locally bijective maps. -/
scoped instance wEqualsLocallyBijectiveOverOpen {X : RingedSpace.{u, u}} (W : Opens X.carrier) :
    ((Opens.grothendieckTopology X.carrier).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u}
    ((Opens.grothendieckTopology X.carrier).over W)

end Stacks.Topology.RingedSpaceSheafifyOpens

end
