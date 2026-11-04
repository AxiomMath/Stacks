module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitDegrees
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-!
# Abelianness of sheaves of modules over a ringed space

For a ringed space `Z`, the category of sheaves of `𝒪_Z`-modules is abelian.

## Main definitions

* `Stacks.Cohomology.ProjectionFormulaPerfect.abelianModulesRingSheaf`: the abelian structure on
  the category of sheaves of modules over `structureSheafRing Z`.

## Implementation notes

The instance is stated at the ring sheaf `structureSheafRing Z`, rather than at
`KFlatDerivedPullback.Modules Z` as
`Stacks.Cohomology.DerivedPullbackTensor.abelianModulesSheafTensor` is, since the two are
identified only up to `implicit_reducible` transparency, which instance synthesis does not use. Its
hypotheses come from the local instances `hasSheafifyOpens` and `wEqualsLocallyBijectiveOpens`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The reduction of a perfect complex to a strictly perfect one -/

section Reduction

attribute [local instance] hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- The category of sheaves of modules over the structure sheaf of rings of a ringed space `Z`
is abelian. -/
@[instance_reducible] local instance abelianModulesRingSheaf (Z : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (structureSheafRing Z)) :=
  _root_.SheafOfModules.instAbelian _

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose

end Reduction

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
